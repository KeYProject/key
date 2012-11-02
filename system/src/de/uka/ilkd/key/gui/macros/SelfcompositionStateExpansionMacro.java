package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import java.util.Set;

/**
 * The macro SelfcompositionStateExpansionMacro applies rules to extract
 * the self-composed states after the merge of the symbolic execution goals
 * which is included in the proof obligation generation from information flow
 * contracts. This macro splits the goal.
 * 
 * The rules that are applied can be set in {@link #ADMITTED_RULES}.
 * 
 * @author christoph
 */
public class SelfcompositionStateExpansionMacro extends AbstractPropositionalExpansionMacro {
    
    @Override 
    public String getName() {
        return "Self-composition state expansion";
    }

    @Override 
    public String getDescription() {
        return "Extract the self-composed states after the merge of the "
                + "symbolic execution goals which is included in the proof "
                + "obligation generation from information flow contracts.";
    }

    private static final String[] ADMITTED_RULES = {
        "andLeft", "orLeft", "impRight"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    @Override
    protected Set<String> getAdmittedRuleNames() {
        return ADMITTED_RULES_SET;
    }

    @Override
    protected boolean ruleApplicationInContextAllowed(RuleApp ruleApp, PosInOccurrence pio, Goal goal) {
        String ruleName = ruleApp.rule().name().toString();
        if ("andLeft".equals(ruleName) &&
            pio.constrainedFormula().formula().op() instanceof UpdateApplication) {
            return false;
        } else {
            return true;
        }
    }

}
