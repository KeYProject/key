/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 * The macro FullPropositionalExpansionMacro apply rules to decompose propositional toplevel
 * formulas; it even splits the goal if necessary.
 *
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 *
 * @author mattias ulbrich
 */
public class FullPropositionalExpansionMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional Expansion (w/ Splits)";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; "
            + "splits the goal if necessary";
    }

    @Override
    public String getScriptCommandName() {
        return "split-prop";
    }

    private static final String[] ADMITTED_RULES =
        { "andLeft", "orRight", "impRight", "notLeft", "notRight", "close", "andRight", "orLeft",
            "impLeft", "closeTrue", "closeFalse", "true_left", "false_right",
            // "ifthenelse_split", "ifthenelse_split_for",
            "equivLeft", "equivRight" };

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
