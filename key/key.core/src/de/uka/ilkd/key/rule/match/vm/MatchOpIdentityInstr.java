package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchOpIdentityInstr extends Instruction<Operator> {

    public MatchOpIdentityInstr(Operator op) {
        super(op);
    }

    public MatchConditions match(Term p_op, MatchConditions mc,
            Services services) {
        return op.match(p_op.op(), mc, services);
    }

}
