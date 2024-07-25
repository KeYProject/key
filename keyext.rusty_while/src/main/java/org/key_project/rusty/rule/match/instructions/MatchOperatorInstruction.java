package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.op.Operator;
import org.key_project.rusty.Services;
import org.key_project.rusty.rule.MatchConditions;

public interface MatchOperatorInstruction extends MatchInstruction {

    MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
                          Services services);

}