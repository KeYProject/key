package de.uka.ilkd.key.rule.match.vm.instructions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.SortException;
import de.uka.ilkd.key.rule.match.vm.TermNavigator;

public class MatchSortDependingFunctionInstruction extends
        Instruction<SortDependingFunction> {

    private final GenericSort genericSortOfOp; 
    
    protected MatchSortDependingFunctionInstruction(SortDependingFunction op) {
        super(op);
        if (op.getSortDependingOn() instanceof GenericSort) {
            genericSortOfOp = (GenericSort)op.getSortDependingOn();
        } else {
            genericSortOfOp = null;
        }
    }

    /**
     * matches the depending sort of this instructions sort depending function against the given sort. If a match is possible 
     * the resulting match conditions are returned otherwise {@code null} is returned.
     * @param dependingSortToMatch the depending {@link Sort} of the concrete function to be matched   
     * @param matchConditions the {@link MatchConditions} accumulated so far 
     * @return <code>null</code> if failed the resulting match conditions 
     * otherwise the resulting {@link MatchConditions} 
     */
    private MatchConditions matchSorts(Sort dependingSortToMatch, MatchConditions matchConditions, Services services) {
        // This restriction has been dropped for free generic sorts to prove taclets correct
        //         assert !(s2 instanceof GenericSort)
        //               : "Sort s2 is not allowed to be of type generic.";
        MatchConditions result = null;
        if (genericSortOfOp != null) {
            final GenericSortCondition c 
                = GenericSortCondition.createIdentityCondition(genericSortOfOp, dependingSortToMatch);                                               
            if(c != null) {
                try {                   
                    result = matchConditions.setInstantiations(matchConditions.getInstantiations().add(c, services));
                } catch(SortException e) {
                    result = null;
                }
            }                  
        } else if (op.getSortDependingOn() == dependingSortToMatch) {
            result = matchConditions;
        }               
        return result;
    }
    
    
    /**
     * Tries to match the top level operator of the given term with this instruction's sort depending function symbol.
     * It returns the resulting match conditions or {@code null} if no match is possible because the top level operator is
     * not a sort depending function or the resulting constraints on the sorts are unsatisfiable.
     * @param instantiationCandidate the {@link Term} to be matched
     * @param matchConditions the {@link MatchConditions} specifying the constraints to be considered
     * @param services the {@link Services} 
     */
    @Override    
    public final MatchConditions match(Term instantiationCandidate, 
                                       MatchConditions matchConditions,
                                       Services services) {  
        MatchConditions result = null; 
        if(instantiationCandidate.op() instanceof SortDependingFunction) {      
            final SortDependingFunction sdp = (SortDependingFunction)instantiationCandidate.op();
            if(op.isSimilar(sdp)) {
                result = matchSorts(sdp.getSortDependingOn(), matchConditions, services);
            }
        } 
        return result;
    }
    
    
    /**
     * {@inheritDoc}
     */
    @Override
    public MatchConditions match(TermNavigator termPosition, MatchConditions mc,
            Services services) {
        final MatchConditions result = match(termPosition.getCurrentSubterm(), mc, services);
        if (result != null) {
            termPosition.gotoNext();
        }
        return result;
    }

}
