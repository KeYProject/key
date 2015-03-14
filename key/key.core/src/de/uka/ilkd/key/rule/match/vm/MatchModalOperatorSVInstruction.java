package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ModalOperatorSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchModalOperatorSVInstruction extends
        Instruction<ModalOperatorSV> {

    public MatchModalOperatorSVInstruction(ModalOperatorSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(Term p_op, MatchConditions mc,
            Services services) {
        return op.match(p_op.op(), mc, services);
    }

}
