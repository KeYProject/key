/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * This macro applies only update simplification rules.
 *
 * @author Richard Bubel
 */
public class UpdateSimplificationMacro extends AbstractPropositionalExpansionMacro {

    public static final String UPDATE_SIMPLIFICATION_ONLY = "Update Simplification Only";

    private static final String[] ADMITTED_RULE_NAMES =
        { "simplifyUpdate1", "simplifyUpdate2", "simplifyUpdate3", "sequentialToParallel1",
            "sequentialToParallel2", "sequentialToParallel3", "applyOnRigidTerm",
            "applyOnRigidFormula", "applyOnElementary", "applyOnParallel", "applyOnSkip",
            "applyOnPV", "parallelWithSkip1", "parallelWithSkip2", "applySkip1", "applySkip2", };

    private static final Set<String> ADMITTED_RULE_NAMES_AS_SET = new HashSet<>();
    static {
        Collections.addAll(ADMITTED_RULE_NAMES_AS_SET, ADMITTED_RULE_NAMES);
    }


    @Override
    public String getName() {
        return UPDATE_SIMPLIFICATION_ONLY;
    }

    @Override
    public String getCategory() {
        return "Simplification";
    }

    @Override
    public String getScriptCommandName() {
        return "simp-upd";
    }

    @Override
    public String getDescription() {
        return "Applies only update simplification rules";
    }

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULE_NAMES_AS_SET;
    }

    @Override
    protected boolean allowOSS() {
        return true;
    }

}
