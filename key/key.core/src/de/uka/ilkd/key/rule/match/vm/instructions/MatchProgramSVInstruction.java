package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;
import de.uka.ilkd.key.util.Debug;

public class MatchProgramSVInstruction extends MatchSchemaVariableInstruction<ProgramSV> implements MatchOperatorInstruction {

    public MatchProgramSVInstruction(ProgramSV sv) {
        super(sv);
    }

    
    /**
     * tries to add the pair <tt>(this,pe)</tt> to the match conditions. If
     * possible the resulting match conditions are returned, otherwise
     * <tt>null</tt>. Such an addition can fail, e.g. if already a pair
     * <tt>(this,x)</tt> exists where <tt>x<>pe</tt>
     */
    protected MatchConditions addInstantiation(ProgramElement pe,
            MatchConditions matchCond, 
            Services services) {

        final SVInstantiations instantiations = matchCond.getInstantiations();
        final Object inMap = instantiations.getInstantiation(op);

        if (inMap == null) {            
            try {
                return matchCond
                        .setInstantiations(instantiations.add(op, pe, services));
            } catch (IllegalInstantiationException e) {
                Debug
                .out("Exception thrown by class Taclet at setInstantiations");
            }
        } else {
            Object peForCompare = pe;
            if (inMap instanceof Term) {
                try {
                    peForCompare = services.getTypeConverter()
                            .convertToLogicElement(
                                    pe,
                                    matchCond.getInstantiations()
                                    .getExecutionContext());                    
                } catch (RuntimeException re) {
                    return null;
                }
            }
            if (inMap.equals(peForCompare)) {
                return matchCond;
            }
        }
        return null;
    }

    
    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Operator instantiationCandidate,
            MatchConditions matchConditions, Services services) {
        if (instantiationCandidate instanceof ProgramElement) {
            return match((ProgramElement)instantiationCandidate, matchConditions, services);
        }
        return null;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(Term instantiationCandidate,  MatchConditions matchCond, Services services) {
        final ProgramSVSort svSort = (ProgramSVSort)op.sort();

        if (svSort.canStandFor(instantiationCandidate)) {
            return addInstantiation(instantiationCandidate, matchCond, services);
        }
        
        return null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(ProgramElement instantiationCandidate,  MatchConditions matchCond, Services services) {
        final ProgramSVSort svSort = (ProgramSVSort)op.sort();

        if (svSort.canStandFor(instantiationCandidate, 
                matchCond.getInstantiations().getExecutionContext(), services)) {
            return addInstantiation(instantiationCandidate, matchCond, services);
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
            termPosition.gotoNextSibling();
        }
        return result;
    }
}
