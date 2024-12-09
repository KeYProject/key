/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 * The macro PropositionalExpansionMacro apply rules to decompose propositional toplevel formulas;
 * but does not split the goal.
 *
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 *
 * @author mattias ulbrich
 */
public class PropositionalExpansionMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional Expansion (w/o Splits)";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; "
            + "does not split the goal.";
    }

    @Override
    public String getScriptCommandName() {
        return "nosplit-prop";
    }

    private static final String[] ADMITTED_RULES = { "andLeft", "orRight", "impRight", "notLeft",
        "notRight", "close", "closeTrue", "closeFalse", "true_left", "false_right" };

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
