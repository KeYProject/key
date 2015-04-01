package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchOpIdentityInstruction<T extends Operator> extends Instruction<T> {

    public MatchOpIdentityInstruction(T op) {
        super(op);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final MatchConditions match(Term instantiationCandidate, MatchConditions matchCond, Services services) {
        if(instantiationCandidate.op() == op) {
            return matchCond;
        }
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {        
        MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }
}
