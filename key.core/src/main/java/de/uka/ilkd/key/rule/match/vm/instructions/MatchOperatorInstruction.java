package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;

public interface MatchOperatorInstruction extends MatchInstruction {
    
    public MatchConditions match(Operator instantiationCandidate,  MatchConditions matchConditions, Services services);

}
