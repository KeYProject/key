package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public final class BoundedNumericalQuantifier extends AbstractOperator {
     
    /** the bounded sum operator */
    public static final BoundedNumericalQuantifier BSUM = new BoundedNumericalQuantifier(new Name("\\bSum"));

    private BoundedNumericalQuantifier(Name name) {
        super(name, 3, new Boolean[]{false, false, true}, true);
    }
    
    
    @Override    
    public Sort sort(ArrayOfTerm terms) {
        return terms.getTerm(2).sort();
    }
    
    
    @Override
    public boolean additionalValidTopLevel(Term term) {
        return true;
    }
 
    
    public Sort argSort(int i) {
	return Sort.ANY;
    }
}
