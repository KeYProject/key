package de.uka.ilkd.key.gui.macros;

import java.util.Set;

public class PropositionalExpansionMacro extends AbstractPropositionalExpansionMacro {

    @Override 
    public String getName() {
        return "Propositional expansion (w/o splits)";
    }
    
    @Override 
    public String getDescription() {
        return "Apply rules to decompose propositional toplevel formulas; " +
                "does not split the goal.";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orRight", "impRight", "notLeft", "notRight", "close"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

}
