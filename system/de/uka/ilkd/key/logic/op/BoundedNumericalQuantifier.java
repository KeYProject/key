package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public class BoundedNumericalQuantifier extends Op {
     
    BoundedNumericalQuantifier(Name name) {
        super(name, 3);
    }
    
    public Sort sort(Term[] term) {
        return term[2].sort();
    }

    public boolean validTopLevel(Term term) {
        return term.arity()==arity();
    }

    public Sort argSort(int i) {
	return Sort.ANY;
    }
}