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
     * tries to match sort <code>s1</code> to fit sort <code>s2</code>
     * @param dependingSortToMatch concrete Sort 
     * @param matchCond the MatchConditions up to now
     * @return <code>null</code> if failed the resulting match conditions 
     * otherwise 
     */
    private MatchConditions matchSorts(Sort dependingSortToMatch, MatchConditions matchCond, Services services) {
        // This restriction has been dropped for free generic sorts to prove taclets correct
        //         assert !(s2 instanceof GenericSort)
        //               : "Sort s2 is not allowed to be of type generic.";
        MatchConditions result = null;
        if (genericSortOfOp != null) {
            final GenericSortCondition c 
                = GenericSortCondition.createIdentityCondition(genericSortOfOp, dependingSortToMatch);                                               
            if(c != null) {
                try {                   
                    result = matchCond.setInstantiations(matchCond.getInstantiations().add(c, services));
                } catch(SortException e) {
                    result = null;
                }
            }                  
        } else if (op.getSortDependingOn() == dependingSortToMatch) {
            result = matchCond;
        }               
        return result;
    }
    
    
    /**
     * Taking this sortdepending function as template to be matched against <code>op</code>, 
     * the necessary conditions are returned or null if not unifiable (matchable).
     * A sortdepending function is matched successfully against another sortdepending function
     * if the sorts can be matched and they are of same kind.      
     */
    @Override    
    public final MatchConditions match(Term subst, 
                                       MatchConditions mc,
                                       Services services) {  
        MatchConditions result = null; 
        if(subst.op() instanceof SortDependingFunction) {      
            final SortDependingFunction sdp = (SortDependingFunction)subst.op();
            if(op.isSimilar(sdp)) {
                result = matchSorts(sdp.getSortDependingOn(), mc, services);
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
