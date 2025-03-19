/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 *
 * @author christoph
 */
public class PropositionalExpansionWithSimplificationMacro
        extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional Expansion (w/o Splits) + Simplification";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; "
            + "does not split the goal. Applies one step simplifications.";
    }

    private static final String[] ADMITTED_RULES = { "andLeft", "orRight", "impRight", "notLeft",
        "notRight", "close", "One Step Simplification" };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected boolean allowOSS() {
        return false;
    }
}
