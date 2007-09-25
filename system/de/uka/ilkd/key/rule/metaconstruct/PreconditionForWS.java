package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class PreconditionForWS extends AbstractMetaOperator {

    public PreconditionForWS() {
        super(new Name("#getPreForWS"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return term.sub(0).sub(0);
    }
    
    public Sort sort(Term[] term){
        return Sort.FORMULA;
    }

}
