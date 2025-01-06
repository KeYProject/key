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
import org.key_project.prover.rules.RuleSet;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.TacletIndex;
import org.key_project.rusty.proof.io.consistency.FileRepo;
import org.key_project.rusty.rule.BuiltInRule;
import org.key_project.rusty.rule.Taclet;
import org.key_project.rusty.rule.tacletbuilder.TacletBuilder;
import org.key_project.rusty.settings.ProofSettings;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.jspecify.annotations.NonNull;

public class InitConfig {
    /**
     * the services class allowing to access information about the underlying program model
     */
    private final Services services;

    private ProofSettings settings;

    private ImmutableList<Taclet> taclets = ImmutableSLList.nil();

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

    /** HashMap for quick lookups taclet name->taclet */
    private Map<Name, Taclet> activatedTacletCache = null;


    // -------------------------------------------------------------------------
    // constructors
    // -------------------------------------------------------------------------

    public InitConfig(Services services) {
        this.services = services;
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

    public InitConfig copy() {
        return copyWithServices(services.copyPreservesLDTInformation());
    }

    // TODO fix ProofSettings
    public InitConfig copyWithServices(Services services) {
        InitConfig ic = new InitConfig(services);
        if (settings != null) {
            ic.setSettings(new ProofSettings());// settings));
        }

        ic.setTaclet2Builder(
            (HashMap<Taclet, TacletBuilder<? extends Taclet>>) taclet2Builder.clone());
        ic.taclets = taclets;
        ic.fileRepo = fileRepo; // TODO: copy instead? delete via dispose method?
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
        for (Taclet t : taclets) {
            TacletBuilder<? extends Taclet> b = taclet2Builder.get(t);
            if (b != null) {
                t = b.getTaclet();
            }

            if (t != null) {
                tacletCache.put(t.name(), t);
            }
        }
        activatedTacletCache = Collections.unmodifiableMap(tacletCache);
    }
}
