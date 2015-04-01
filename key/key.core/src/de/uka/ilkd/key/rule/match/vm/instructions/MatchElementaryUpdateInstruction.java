package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.match.vm.TacletMatchProgram;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchElementaryUpdateInstruction extends Instruction<ElementaryUpdate> {

    private final Instruction<? extends UpdateableOperator> leftHandSide;
    
    @SuppressWarnings("unchecked")
    protected MatchElementaryUpdateInstruction(ElementaryUpdate op) {
        super(op);
        if (op.lhs() instanceof LocationVariable) {
            leftHandSide = new MatchOpIdentityInstruction<LocationVariable>((LocationVariable)op.lhs());        
        } else {
            assert op.lhs() instanceof ProgramSV;
            leftHandSide = (Instruction<? extends UpdateableOperator>) TacletMatchProgram.getMatchInstructionForSV((ProgramSV)op.lhs());
        }
    }

    @Override
    public MatchConditions match(Term instantiationCandidate,
            MatchConditions matchCond, Services services) {
        if (instantiationCandidate.op() != op) {
            matchCond = leftHandSide.match(instantiationCandidate, matchCond, services);
        }
        return matchCond;
    }
    
    @Override
    public MatchConditions match(TermNavigator termPosition,
            MatchConditions matchConditions, Services services) {
        final MatchConditions result = match(termPosition.getCurrentSubterm(), matchConditions, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }
}
