package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchVariableSVInstr extends Instruction<VariableSV> {

    protected MatchVariableSVInstr(VariableSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(Term p_vartermCandidate, MatchConditions mc,
            Services services) {
        return op.match(p_vartermCandidate, mc, services);
    }

}
