// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * Standard first-order substitution operator, resolving clashes but not
 * preventing (usually unsound) substitution of non-rigid terms across modal
 * operators. Currently, only the subclass <code>WarySubstOp</code> is used
 * and accessible through the key parser.
 */
public abstract class SubstOp extends AbstractOperator {
    
    protected SubstOp(Name name) {
	super(name, 2, new Boolean[]{false, true}, true);
    }
    

    /**
     * @return sort of the second subterm or throws an
     * IllegalArgumentException if the given term has no correct (2=) arity
     */
    @Override
    public Sort sort(ImmutableArray<Term> terms) {
	if(terms.size() == 2) {
	    return terms.get(1).sort();
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
    @Override    
    protected boolean additionalValidTopLevel(Term term){
	if(term.varsBoundHere(1).size() != 1) { 
	    return false;
	}
	Sort substSort = term.sub(0).sort();
	Sort varSort = term.varsBoundHere(1).get(0).sort();       
	return substSort.extendsTrans(varSort);
    }

    
    /**
     * Apply this substitution operator to <code>term</code>, which
     * has this operator as top-level operator
    * @param services TODO
     */
    public abstract Term apply(Term term, TermServices services);// {
//	QuantifiableVariable v = term.varsBoundHere(1).getQuantifiableVariable(0);
//	ClashFreeSubst cfSubst = new ClashFreeSubst(v, term.sub(0));
//	Term res = cfSubst.apply(term.sub(1));
//	return res;
//    }
}