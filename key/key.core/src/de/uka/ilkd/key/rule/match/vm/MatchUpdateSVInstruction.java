package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.UpdateSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchUpdateSVInstruction extends Instruction<UpdateSV> {

    protected MatchUpdateSVInstruction(UpdateSV op) {
        super(op);
    }

    @Override
    public MatchConditions match(Term p_updateCandidate, MatchConditions mc,
            Services services) {
        return op.match(p_updateCandidate, mc, services);
    }

}
