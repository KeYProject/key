// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Standard first-order substitution operator, resolving clashes but not
 * preventing (usually unsound) substitution of non-rigid terms across modal
 * operators. Currently, only the subclass <code>WarySubstOp</code> is used
 * and accessible through the key parser.
 */
public abstract class SubstOp extends AbstractOperator {
    
    protected SubstOp(Name name) {
	super(name, 2);
    }
    

    /**
     * @return sort of the second subterm or throws an
     * IllegalArgumentException if the given term has no correct (2=) arity
     */
    public Sort sort(ArrayOfTerm terms) {
	if(terms.size() == 2) {
	    return terms.getTerm(1).sort();
	}
	else throw new IllegalArgumentException("Cannot determine sort of "+
						"invalid term (Wrong arity).");
    }    
    

    /**
     * @return true iff the sort of the subterm 0 of the given term
     * has the same sort as or a subsort of the variable to be substituted 
     * and the
     * term's arity is 2 and the numer of variables bound there is 0
     * for the 0th subterm and 1 for the 1st subterm.
     */
    public boolean validTopLevel(Term term){
	if(term.arity() != arity()) {
	    return false;
	}
	if(term.varsBoundHere(0).size() != 0) {
	    return false;
	}
	if(term.varsBoundHere(1).size() != 1) { 
	    return false;
	}
	Sort substSort = term.sub(0).sort();
	Sort varSort = term.varsBoundHere(1).getQuantifiableVariable(0).sort();       
	return substSort.extendsTrans(varSort);
    }

    
    /**
     * Apply this substitution operator to <code>term</code>, which
     * has this operator as top-level operator
     */
    public Term apply(Term term) {
	QuantifiableVariable v = term.varsBoundHere(1).getQuantifiableVariable(0);
	ClashFreeSubst cfSubst = new ClashFreeSubst(v, term.sub(0));
	Term res = cfSubst.apply(term.sub(1));
	return res;
    }
}
