// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule;

import java.util.HashSet;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/**
 * The bound uniqueness checker ensures that schemavariables can be bound
 * at most once in the <tt>\find</tt> and <tt>\assumes</tt> part of a taclet. The justification for this restriction is to
 * prevent the user to write taclets that match only in very rare cases, e.g.
 * <code>
 *   \assumes (==>\forall var; phi)
 *   \find (\forall var; phi ==>)
 * </code>
 * would nearly never match, as <tt>var</tt> would be required to match 
 * the same object.
 */
public class BoundUniquenessChecker {

    private HashSet<QuantifiableVariable> boundVars = new LinkedHashSet<QuantifiableVariable>();
    private ImmutableList<Term> terms = ImmutableSLList.<Term>nil();

    public BoundUniquenessChecker(Sequent seq) {
        addAll(seq);
    }

    public BoundUniquenessChecker(Term t, Sequent seq) {
	addTerm(t);
	addAll(seq);
    }

    /**
     * adds <tt>term</tt> to the list of terms to include in  
     * the uniqueness check
     * @param term a Term  
     */
    public void addTerm(Term term) {
	terms = terms.prepend(term);	
    }

    /**
     * adds all formulas in the sequent to the list of terms to
     * include in the uniqueness check  
     * @param seq the Sequent with the formulas to add
     */
    public void addAll(Sequent seq) {
	for (final SequentFormula cf : seq) {
	    terms = terms.prepend(cf.formula());	
	}
    }

    //recursive helper
    private boolean correct(Term t) {
	/* Note that a term can bound a variable in several
	 * subterms. 
         */
        final HashSet<QuantifiableVariable> localVars = new LinkedHashSet<QuantifiableVariable>(10);
        
        for (int i = 0, ar = t.arity(); i<ar; i++) {
            for (int j=0, sz = t.varsBoundHere(i).size(); j<sz; j++) {
                final QuantifiableVariable qv
                = t.varsBoundHere(i).get(j);
                if (boundVars.contains(qv)) {
                    return false;
                } else {
                    localVars.add(qv);
                }
            }
        }	

        boundVars.addAll(localVars);
        
	for (int i = 0, ar = t.arity(); i < ar; ++i) {
	    if (!correct(t.sub(i))) {
		return false;
	    }
	}
	return true;
    }


    /** 
     * returns true if any variable is bound at most once in the
     * given set of terms
     */
    public boolean correct() {
        for (final Term term : terms) {
            if (!correct(term)) {       
                return false;
            }	        
        }
        return true;    
    }

}
