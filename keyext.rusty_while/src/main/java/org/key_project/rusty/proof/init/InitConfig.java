/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;


import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.NamespaceSet;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.settings.ProofSettings;

import java.util.HashMap;


public class InitConfig {
    /**
     * the services class allowing to access information about the underlying program model
     */
    private final Services services;

    private ProofSettings settings;

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

    public Services getServices() {
        return services;
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
//    public Namespace<RuleSet> ruleSetNS() {
//        return namespaces().ruleSets();
//    }


    /**
     * returns the variable namespace of this initial configuration
     */
    public Namespace<QuantifiableVariable> varNS() {
        return namespaces().variables();
    }


    /**
     * returns the program variable namespace of this initial configuration
     */
    public Namespace<ProgramVariable> progVarNS() {
        return namespaces().programVariables();
    }
}
