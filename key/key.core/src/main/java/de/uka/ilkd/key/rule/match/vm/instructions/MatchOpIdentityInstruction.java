package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

/**
 * The match instruction reports a success if the top level operator of the term to be matched is the <strong>same</strong>(identical) operator
 * like the one for which this instruction has been instantiated
 * @param <T> the type of the operator used as template
 */
public class MatchOpIdentityInstruction<T extends Operator> extends Instruction<T> implements MatchOperatorInstruction {

    public MatchOpIdentityInstruction(T op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions match(Term instantiationCandidate, MatchConditions matchConditions, Services services) {
        if(instantiationCandidate.op() == op) {
            return matchConditions;
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Operator instantiationCandidate,
            MatchConditions matchConditions, Services services) {
        if(instantiationCandidate == op) {
            return matchConditions;
        }
        return null;    
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions matchConditions,
            Services services) {        
        MatchConditions result = match(termPosition.getCurrentSubterm(), matchConditions, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
