package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class MetaBool2Logic extends AbstractMetaOperator {

    public MetaBool2Logic() {
        super(new Name("#bool2Logic"), 1);      
    }

    public Term calculate(Term term, SVInstantiations svInst, Services services) {        
        return term.sub(0).sort() == Sort.FORMULA ? term.sub(0) : 
            TermBuilder.DF.equals(term.sub(0), TermBuilder.DF.TRUE(services));
    }
    
    /**
     * determines the sort of the {@link Term} if it would be created using this
     * Operator as top level operator and the given terms as sub terms. The
     * assumption that the constructed term would be allowed is not checked.
     * @param term an array of Term containing the subterms of a (potential)
     * term with this operator as top level operator
     * @return sort of the term with this operator as top level operator of the
     * given substerms
     */
    public Sort sort(Term[] term) {
        return sort();
    }

    public Sort sort() {
        return Sort.FORMULA;
    }
    
}
