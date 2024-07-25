package org.key_project.rusty.rule.match.instructions;

import org.key_project.logic.SyntaxElementCursor;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.rusty.Services;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.rule.MatchConditions;

/**
 * The match instruction reports a success if the top level operator of the term to be matched is
 * the <strong>same</strong> modality like the one for which this instruction has been
 * instantiated
 */
public class MatchModalityInstruction extends Instruction<Modality>
        implements MatchOperatorInstruction {

    public MatchModalityInstruction(Modality op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions match(Term t, MatchConditions matchConditions,
                                       Services services) {
        return match(t.op(), matchConditions, services);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Operator instantiationCandidate, MatchConditions matchConditions,
                                 Services services) {
        if (instantiationCandidate instanceof Modality mod1 && mod1.kind() == op.kind()) {
            return matchConditions;
        } else {
            return null;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(SyntaxElementCursor cursor, MatchConditions matchConditions,
                                 Services services) {
        return match((Term) cursor.getCurrentNode(), matchConditions, services);
    }

}