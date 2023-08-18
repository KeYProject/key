/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.*;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.TacletIndexKit;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.proof.mgt.RuleJustification;
import de.uka.ilkd.key.proof.mgt.RuleJustificationByAddRules;
import de.uka.ilkd.key.proof.mgt.RuleJustificationInfo;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.tacletbuilder.TacletBuilder;
import de.uka.ilkd.key.settings.ProofSettings;

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * an instance of this class describes the initial configuration of the prover. This includes sorts,
 * functions, heuristics, and variables namespaces, information on the underlying java model, and a
 * set of rules.
 */
public class InitConfig {

    /**
     * the services class allowing to access information about the underlying program model
     */
    private final Services services;

    private RuleJustificationInfo justifInfo = new RuleJustificationInfo();


    private ImmutableList<Taclet> taclets = ImmutableSLList.nil();

    /**
     * maps categories to their default choice (both represented as Strings), which is used if no
     * other choice is specified in the problemfile
     */
    private Map<String, String> category2DefaultChoice;

    /**
     * maps taclets to their TacletBuilders. This information is needed when a taclet contains
     * GoalTemplates annotated with taclet-options because in this case a new taclet has to be
     * created containing only those GoalTemplates whose options are activated and those who don't
     * belong to any specific option.
     */
    private HashMap<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder = new LinkedHashMap<>();

    /**
     * Set of the rule options activated for the current proof. The rule options ({@link Choice}s)
     * allow to use different ruleset modelling or skipping certain features (e.g. nullpointer
     * checks when resolving references)
     */
    private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.nil();

    /** HashMap for quick lookups taclet name->taclet */
    private Map<Name, Taclet> activatedTacletCache = null;

    /** the fileRepo which is responsible for consistency between source code and proof */
    private FileRepo fileRepo;

    private String originalKeYFileName;

    private ProofSettings settings;



    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public InitConfig(Services services) {
        this.services = services;

        category2DefaultChoice = new HashMap<>(
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices());
    }


    // -------------------------------------------------------------------------
    // internal methods
    // -------------------------------------------------------------------------



    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    /**
     * returns the Services of this initial configuration providing access to the used program model
     *
     * @return the Services of this initial configuration
     */
    public final Services getServices() {
        return services;
    }


    public Profile getProfile() {
        return services.getProfile();
    }


    /**
     * Adds a default option for a category. It does override previous default choices.
     *
     * @return true if the default was successfully set
     */
    public boolean addCategoryDefaultChoice(@Nonnull String category, @Nonnull String choice) {
        if (!category2DefaultChoice.containsKey(category)) {
            category2DefaultChoice.put(category, choice);
            return true;
        }
        return false;
    }

    /**
     * Adds default choices given in {@code init}. Not overriding previous default choices.
     */
    public void addCategory2DefaultChoices(@Nonnull Map<String, String> init) {
        boolean changed = false;
        for (final Map.Entry<String, String> entry : init.entrySet()) {
            changed = addCategoryDefaultChoice(entry.getKey(), entry.getValue()) || changed;
        }
        if (changed) {
            // FIXME weigl: I do not understand why the default choices are back progragated!
            // For me this is a design flaw.
            Map<String, String> clone =
                new HashMap<>(category2DefaultChoice);
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(clone);
            // invalidate active taclet cache
            activatedTacletCache = null;
        }
    }


    public void setTaclet2Builder(HashMap<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder) {
        this.taclet2Builder = taclet2Builder;
    }


    /**
     * {@link Taclet}s are constructed using {@link TacletBuilder}s this map contains the pair of a
     * taclet and its builder which is important as goals of a taclet may depend of the selected
     * choices. Instead of creating all possible combinations in advance this is done by demand
     *
     * @return the map from a taclet to its builder
     */
    public HashMap<Taclet, TacletBuilder<? extends Taclet>> getTaclet2Builder() {
        return taclet2Builder;
    }


    /**
     * sets the set of activated choices of this initial configuration. For categories without a
     * specified choice the default choice contained in category2DefaultChoice is added.
     */
    public void setActivatedChoices(ImmutableSet<Choice> activatedChoices) {
        category2DefaultChoice =
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();

        HashMap<String, String> c2DC = new HashMap<>(category2DefaultChoice);
        for (final Choice c : activatedChoices) {
            c2DC.remove(c.category());
        }

        ImmutableList<Choice> category2DefaultChoiceList = ImmutableSLList.nil();
        for (final String s : c2DC.values()) {
            final Choice c = choiceNS().lookup(new Name(s));
            if (c != null) {
                category2DefaultChoiceList = category2DefaultChoiceList.prepend(c);
            }
        }
        this.activatedChoices = activatedChoices
                .union(
                    DefaultImmutableSet.fromImmutableList(category2DefaultChoiceList));

        // invalidate active taclet cache
        activatedTacletCache = null;
    }


    /**
     * Returns the choices which are currently active. For getting the active choices for a specific
     * proof, <code>getChoices</code> in <code>de.uka.ilkd.key.proof.Proof
     * </code> has to be used.
     */
    public ImmutableSet<Choice> getActivatedChoices() {
        return activatedChoices;
    }


    public void addTaclets(Collection<Taclet> tacs) {
        taclets = taclets.append(tacs);
        this.activatedTacletCache = null;
    }

    public void setTaclets(ImmutableList<Taclet> tacs) {
        taclets = tacs;
        // invalidate active taclet cache
        this.activatedTacletCache = null;
    }

    public void setTaclets(Collection<Taclet> tacs) {
        taclets = ImmutableSLList.nil();
        addTaclets(tacs);
        // invalidate active taclet cache
        this.activatedTacletCache = null;
    }

    public ImmutableList<Taclet> getTaclets() {
        return taclets;
    }

    public Taclet lookupActiveTaclet(Name name) {
        if (activatedTacletCache == null) {
            fillActiveTacletCache();
        }
        return activatedTacletCache.get(name);
    }

    /**
     * returns the activated taclets of this initial configuration
     */
    public Collection<Taclet> activatedTaclets() {
        if (activatedTacletCache == null) {
            fillActiveTacletCache();
        }
        return activatedTacletCache.values();
    }


    /**
     * fills the active taclet cache
     */
    private void fillActiveTacletCache() {
        if (activatedTacletCache != null) {
            return;
        }
        final LinkedHashMap<Name, Taclet> tacletCache = new LinkedHashMap<>();
        var choices = Collections.unmodifiableSet(activatedChoices.toSet());
        for (Taclet t : taclets) {
            TacletBuilder<? extends Taclet> b = taclet2Builder.get(t);

            if (t.getChoices().eval(choices)) {
                if (b != null && b.getGoal2Choices() != null) {
                    t = b.getTacletWithoutInactiveGoalTemplates(choices);
                }

                if (t != null) {
                    tacletCache.put(t.name(), t);
                }
            }
        }
        activatedTacletCache = Collections.unmodifiableMap(tacletCache);
    }


    /**
     * returns the built-in rules of this initial configuration
     */
    public ImmutableList<BuiltInRule> builtInRules() {
        Profile profile = getProfile();
        return (profile == null ? ImmutableSLList.nil()
                : profile.getStandardRules().getStandardBuiltInRules());
    }


    /**
     * registers a rule with the given justification at the justification managing
     * {@link RuleJustification} object of this environment.
     */
    public void registerRule(Rule r, RuleJustification j) {
        justifInfo.addJustification(r, j);
    }

    public void registerRuleIntroducedAtNode(RuleApp r, Node node, boolean isAxiom) {
        justifInfo.addJustification(r.rule(), new RuleJustificationByAddRules(node, isAxiom));
    }

    /**
     * registers a list of rules with the given justification at the justification managing
     * {@link RuleJustification} object of this environment. All rules of the list are given the
     * same justification.
     */
    public void registerRules(Iterable<? extends Rule> s, RuleJustification j) {
        for (Rule r : s) {
            registerRule(r, j);
        }
    }

    /**
     * returns the object managing the rules in this environment and their justifications. The
     * object is unique to this environment.
     */
    public RuleJustificationInfo getJustifInfo() {
        return justifInfo;
    }


    /**
     * returns a newly created taclet index for the set of activated taclets contained in this
     * initial configuration
     */
    public TacletIndex createTacletIndex() {
        return TacletIndexKit.getKit().createTacletIndex(activatedTaclets());
    }


    /**
     * returns a new created index for built in rules (at the moment immutable list)
     */
    public BuiltInRuleIndex createBuiltInRuleIndex() {
        return new BuiltInRuleIndex(builtInRules());
    }


    /**
     * returns the namespaces of this initial configuration
     */
    public NamespaceSet namespaces() {
        return services.getNamespaces();
    }

    /**
     * returns the function namespace of this initial configuration.
     *
     * @return a non-null namespace
     */
    public Namespace<Function> funcNS() {
        return namespaces().functions();
    }


    /**
     * returns the sort namespace of this initial configuration
     */
    public Namespace<Sort> sortNS() {
        return namespaces().sorts();
    }


    /**
     * returns the heuristics namespace of this initial configuration
     */
    public Namespace<RuleSet> ruleSetNS() {
        return namespaces().ruleSets();
    }


    /**
     * returns the variable namespace of this initial configuration
     */
    public Namespace<QuantifiableVariable> varNS() {
        return namespaces().variables();
    }


    /**
     * returns the program variable namespace of this initial configuration
     */
    public Namespace<IProgramVariable> progVarNS() {
        return namespaces().programVariables();
    }


    /**
     * returns the choice namespace of this initial configuration
     */
    public Namespace<Choice> choiceNS() {
        return namespaces().choices();
    }


    public void setSettings(ProofSettings newSettings) {
        this.settings = newSettings;
    }


    public ProofSettings getSettings() {
        return settings;
    }


    /**
     * returns a copy of this initial configuration copying the namespaces, the contained JavaInfo
     * while using the immutable set of taclets in the copy
     */
    public InitConfig copy() {
        return copyWithServices(services.copyPreservesLDTInformation());
    }

    /**
     * returns a copy of this initial configuration copying the namespaces, the contained JavaInfo
     * while using the immutable set of taclets in the copy
     */
    public InitConfig deepCopy() {
        return copyWithServices(services.copy(false));
    }


    /**
     * returns a copy of this initial configuration copying the namespaces, the contained JavaInfo
     * while using the immutable set of taclets in the copy
     */
    @SuppressWarnings("unchecked")
    public InitConfig copyWithServices(Services services) {
        InitConfig ic = new InitConfig(services);
        if (settings != null) {
            ic.setSettings(new ProofSettings(settings));
        }
        ic.setActivatedChoices(activatedChoices);
        ic.category2DefaultChoice = new HashMap<>(category2DefaultChoice);
        ic.setTaclet2Builder(
            (HashMap<Taclet, TacletBuilder<? extends Taclet>>) taclet2Builder.clone());
        ic.taclets = taclets;
        ic.originalKeYFileName = originalKeYFileName;
        ic.justifInfo = justifInfo.copy();
        ic.fileRepo = fileRepo; // TODO: copy instead? delete via dispose method?
        return ic;
    }



    @Override
    public String toString() {
        return "Namespaces:" + namespaces() + "\n" + "Services:" + services + "\n" + "Taclets:"
            + getTaclets() + "\n" + "Built-In:" + builtInRules() + "\n";
    }

    public FileRepo getFileRepo() {
        return fileRepo;
    }

    public void setFileRepo(FileRepo fileRepo) {
        this.fileRepo = fileRepo;
    }
}
