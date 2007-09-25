package de.uka.ilkd.key.rule.metaconstruct;

import java.util.*;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class AtPreEquations extends AbstractMetaOperator {

    private static Term updateFormula = null;
    private static HashMap atPreMapping = null;
    
    public static Map getAtPreFunctions(Term t){
        if(t==updateFormula){
            // atPre Functions were already calculated for updateFormula
            return atPreMapping;
        }
        updateFormula = t;
        atPreMapping = new HashMap();
        AbstractPO.createAtPreFunctionsForTerm(t, atPreMapping);
        return atPreMapping;
    }
    
    public AtPreEquations() {
        super(new Name("#atPreEqs"), 1);
    }
    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.MetaOperator#calculate(de.uka.ilkd.key.logic.Term, de.uka.ilkd.key.rule.inst.SVInstantiations, de.uka.ilkd.key.java.Services)
     */
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Map atPreFunctions = getAtPreFunctions(term.sub(0));
        final Iterator it = atPreFunctions.values().iterator();  
        while(it.hasNext()) {            
            services.getNamespaces().functions().add((Function) it.next()); 
        }
        return AbstractPO.buildAtPreDefinitions(atPreFunctions);
    }
                
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#validTopLevel(de.uka.ilkd.key.logic.Term)
     */
    public boolean validTopLevel(Term term) {
        return term.arity()==1 && term.sub(0).sort()==Sort.FORMULA;
    }

    
    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#sort(de.uka.ilkd.key.logic.Term[])
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
    

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.logic.op.Operator#isRigid(de.uka.ilkd.key.logic.Term)
     */
    public boolean isRigid(Term term) {
        return false;
    }

    
    /** (non-Javadoc)
     * by default meta operators do not match anything 
     * @see de.uka.ilkd.key.logic.op.Operator#match(SVSubstitute, de.uka.ilkd.key.rule.MatchConditions, de.uka.ilkd.key.java.Services)
     */
    public MatchConditions match(SVSubstitute subst, MatchConditions mc,
            Services services) {
        return null;
    }
    
}
