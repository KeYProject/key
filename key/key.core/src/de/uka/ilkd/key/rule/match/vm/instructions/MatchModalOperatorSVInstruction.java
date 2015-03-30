package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchModalOperatorSVInstruction extends
        Instruction<ModalOperatorSV> {

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        MatchConditions result = op.match(termPosition.getCurrentSubterm().op(), mc, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
