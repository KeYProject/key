package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class UniqueAnonUpdate extends AbstractMetaOperator {

    public UniqueAnonUpdate() {
        super(new Name("#uniqueAnonUpdate"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return TermFactory.DEFAULT.createAnonymousUpdateTerm(
                AnonymousUpdate.getNewAnonymousOperator(), term.sub(0));
    }

    public Sort sort(){
        return Sort.FORMULA;
    }
    
    /** Unlike other meta operators this one returns a formula
     * not a term.
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
    
}
