package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher.TermNavigator;

public class MatchUpdateSVInstruction extends Instruction<UpdateSV> {

    protected MatchUpdateSVInstruction(UpdateSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        MatchConditions result = op.match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNextSibling();
        }
        return result;
    }

}
