package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * The meta operator inserting the proof obligation for the <tt>inReachableState</tt>
 * predicate
 * @see de.uka.ilkd.key.rule.metaconstruct.InReachableStatePOBuilder
 */
public class CreateInReachableStatePO extends AbstractMetaOperator {

    public CreateInReachableStatePO() {
        super(new Name("#createInReachableStatePO"), 1);
    }
    
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
       
    public Term calculate(Term term, SVInstantiations svInst, Services services) {   
        final InReachableStatePOBuilder po = new InReachableStatePOBuilder(services);
      
        return po.generatePO(term.sub(0));       
    }
    
   
}
