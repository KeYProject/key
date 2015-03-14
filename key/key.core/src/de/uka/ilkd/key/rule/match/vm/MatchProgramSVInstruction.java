package de.uka.ilkd.key.rule.match.vm;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.rule.MatchConditions;

public class MatchProgramSVInstruction extends Instruction<ProgramSV> {

    public MatchProgramSVInstruction(ProgramSV sv) {
        super(sv);
    }

    @Override
    public MatchConditions match(Term p_op, MatchConditions mc,
            Services services) {
        return op.match(p_op.op(), mc, services);
    }

}
