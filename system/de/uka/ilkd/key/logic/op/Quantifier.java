// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

public class Quantifier extends Op {
    
    /** creates a quantifier */
    Quantifier(Name name) {
	super(name);
    }

    /** 
     * @return Sort.FORMULA
     */
     public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }  

    /** 
     * for convenience reasons
     * @return Sort.FORMULA
     */
     public Sort sort(Term term) {
        return Sort.FORMULA;
    }  

    /** @return true iff the subterm at postion 0 has Sort.FORMULA and the
     * arity of the term is 1 and at least one variable is bound.
     */
    public boolean validTopLevel(Term term){
	if (term.arity()==0) return false;
	if (term.varsBoundHere(0).size()==0) return false;
        return term.sub(0).sort().equals(Sort.FORMULA);
    }


   /** @return arity of the Quantifier as int. */
    public int arity() {
	return 1;
    }

}
