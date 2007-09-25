// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Metavariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;

/** An OpTerm is an object that contains an Operator and several subterms. Can be used
 * to represent e.g., function terms or quantifier terms. Instances should never be 
 * accessed via 
 * this interface, use the interface of the superclass Term and construct instances only via
 * a TermFactory instead.
 */
class OpTerm extends Term {

  
    private final ArrayOfTerm subTerm;

    /** depth of the term */
    private final int depth;

    
    /** creates an OpTerm with top operator op, some subterms and a sort
     * @param op Operator at the top of the termstructure that starts
     * here
     * @param subTerm an array containing subTerms (an array with length 0 if
     * there are no more subterms
     */
    public OpTerm(Operator op, Term[] subTerm) {
	super(op, op.sort(subTerm));
	this.subTerm = new ArrayOfTerm(subTerm);
	int max_depth = -1;
	for (int i = 0, sz = subTerm.length; i < sz; i++) {
	    final int subTermDepth = subTerm[i].depth();
            if (subTermDepth > max_depth) {
		max_depth = subTermDepth;	
	    }
	}
        
	depth = max_depth + 1;
        
	if (op instanceof QuantifiableVariable) {
	    freeVars = freeVars.add((QuantifiableVariable) op);
	} else if ( op instanceof Metavariable ) {
            metaVars = metaVars.add ( (Metavariable)op );
        }
	
	fillCaches();	
    }   

    /** @return arity of the term */
    public int arity() {
	return subTerm.size();
    }

    /**@return depth of the term */
    public int depth() {
	return depth;
    }

    /** the nr-th subterm */
    public Term sub(int nr) {
	return subTerm.getTerm(nr);
    }

    /** @return an empty variable list */
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	return EMPTY_VAR_LIST;
    }

 
}









