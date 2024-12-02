/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;


import java.util.*;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.Choice;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.BuiltInRuleIndex;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.TacletIndex;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.rusty.proof.mgt.RuleJustification;
import org.key_project.rusty.proof.mgt.RuleJustificationByAddRules;
import org.key_project.rusty.proof.mgt.RuleJustificationInfo;
import org.key_project.rusty.rule.*;
import org.key_project.rusty.rule.tacletbuilder.TacletBuilder;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NonNull;

public class InitConfig {
    /**
     * the services class allowing to access information about the underlying program model
     */
    private final Services services;

    private RuleJustificationInfo justifInfo = new RuleJustificationInfo();

    private ProofSettings settings;

    private ImmutableList<Taclet> taclets = ImmutableSLList.nil();

    /**
     * maps categories to their default choice (both represented as Strings), which is used if no
     * other choice is specified in the problem file
     */
    private Map<String, String> category2DefaultChoice = new LinkedHashMap<>();

    /**
     * maps taclets to their TacletBuilders. This information is needed when a taclet contains
     * GoalTemplates annotated with taclet-options because in this case a new taclet has to be
     * created containing only those GoalTemplates whose options are activated and those who don't
     * belong to any specific option.
     */
    private HashMap<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder = new LinkedHashMap<>();

    /** the fileRepo which is responsible for consistency between source code and proof */
    private FileRepo fileRepo;

    private String originalKeYFileName;

    /**
     * Set of the rule options activated for the current proof. The rule options ({@link Choice}s)
     * allow to use different ruleset modelling or skipping certain features (e.g. nullpointer
     * checks when resolving references)
     */
    private ImmutableSet<Choice> activatedChoices = DefaultImmutableSet.nil();

    /** HashMap for quick lookups taclet name->taclet */
    private Map<Name, Taclet> activatedTacletCache = null;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public InitConfig(Services services) {
        this.services = services;

        category2DefaultChoice = new HashMap<>(
            ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices());
    }

    // -------------------------------------------------------------------------
    // public interface
    // -------------------------------------------------------------------------

    public Profile getProfile() {
        return services.getProfile();
    }

    public void setSettings(ProofSettings newSettings) {
        this.settings = newSettings;
    }

    public ProofSettings getSettings() {
        return settings;
    }

    /**
     * returns the Services of this initial configuration providing access to the used program model
     *
     * @return the Services of this initial configuration
     */
    public Services getServices() {
        return services;
    }

    public void setTaclet2Builder(HashMap<Taclet, TacletBuilder<? extends Taclet>> taclet2Builder) {
        this.taclet2Builder = taclet2Builder;
    }

    /**
     * {@link Taclet}s are constructed using {@link TacletBuilder}s. This map contains the pair of a
     * taclet and its builder which is important as goals of a taclet may depend on the selected
     * choices. Instead of creating all possible combinations in advance this is done by demand.
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
    }

    public void setTaclets(ImmutableList<Taclet> tacs) {
        taclets = tacs;
    }

    public void setTaclets(Collection<Taclet> tacs) {
        taclets = ImmutableSLList.nil();
        addTaclets(tacs);
    }

    public ImmutableList<Taclet> getTaclets() {
        return taclets;
    }

    public FileRepo getFileRepo() {
        return fileRepo;
    }

    public void setFileRepo(FileRepo fileRepo) {
        this.fileRepo = fileRepo;
    }

    /**
     * returns the built-in rules of this initial configuration
     */
    public ImmutableList<BuiltInRule> builtInRules() {
        Profile profile = getProfile();
        return (profile == null ? ImmutableSLList.nil()
                : profile.getStandardRules().standardBuiltInRules());
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
    public Namespace<@NonNull Function> funcNS() {
        return namespaces().functions();
    }


    /**
     * returns the sort namespace of this initial configuration
     */
    public Namespace<@NonNull Sort> sortNS() {
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
    public Namespace<@NonNull QuantifiableVariable> varNS() {
        return namespaces().variables();
    }


    /**
     * returns the program variable namespace of this initial configuration
     */
    public Namespace<@NonNull ProgramVariable> progVarNS() {
        return namespaces().programVariables();
    }

    /**
     * returns the choice namespace of this initial configuration
     */
    public Namespace<@NonNull Choice> choiceNS() {
        return namespaces().choices();
    }

    public InitConfig copy() {
        return copyWithServices(services.copyPreservesLDTInformation());
    }

    // TODO fix ProofSettings
    public InitConfig copyWithServices(Services services) {
        InitConfig ic = new InitConfig(services);
        if (settings != null) {
            ic.setSettings(new ProofSettings(ProofSettings.DEFAULT_SETTINGS));// settings));
        }

        ic.setTaclet2Builder(
            (HashMap<Taclet, TacletBuilder<? extends Taclet>>) taclet2Builder.clone());
        ic.taclets = taclets;
        ic.fileRepo = fileRepo; // TODO: copy instead? delete via dispose method?
        ic.setActivatedChoices(activatedChoices);
        ic.justifInfo = justifInfo.copy();
        return ic;
    }

    public TacletIndex createTacletIndex() {
        return new TacletIndex(taclets);
    }

    public Taclet lookupActiveTaclet(Name name) {
        if (activatedTacletCache == null) {
            fillActiveTacletCache();
        }
        return activatedTacletCache.get(name);
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
     * Adds default choices given in {@code init}. Not overriding previous default choices.
     */
    public void addCategory2DefaultChoices(@NonNull Map<String, String> init) {
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
     * Adds a default option for a category. It does override previous default choices.
     *
     * @return true if the default was successfully set
     */
    public boolean addCategoryDefaultChoice(@NonNull String category, @NonNull String choice) {
        if (!category2DefaultChoice.containsKey(category)) {
            category2DefaultChoice.put(category, choice);
            return true;
        }
        return false;
    }

    public RuleJustificationInfo getJustifInfo() {
        return justifInfo;
    }

    public BuiltInRuleIndex createBuiltInRuleIndex() {
        return new BuiltInRuleIndex(builtInRules());
    }

    public InitConfig deepCopy() {
        return copyWithServices(services.copy());
    }
}
