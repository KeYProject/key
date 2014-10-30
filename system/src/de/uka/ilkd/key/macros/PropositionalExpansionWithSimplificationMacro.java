/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.macros;

import java.util.Set;

/**
 *
 * @author christoph
 */
public class PropositionalExpansionWithSimplificationMacro extends AbstractPropositionalExpansionMacro {

    @Override
    public String getName() {
        return "Propositional expansion (w/o splits) + simplification";
    }

    @Override
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; " +
                "does not split the goal. Applies one step simplifications.";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orRight", "impRight", "notLeft", "notRight", "close",
        "One Step Simplification"
    };

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