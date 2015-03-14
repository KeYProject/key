package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.TermLabelSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchTermLabelSVInstruction extends Instruction<TermLabelSV> {

    public MatchTermLabelSVInstruction(TermLabelSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(Term p_op, MatchConditions mc,
            Services services) {
        return op.match(p_op, mc, services);
    }

}
