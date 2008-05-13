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
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;


/**
 * A SubstitutionTerm is an object that contains an Operator two subterms. 
 * and one variable
 * Instances should never be accessed via 
 * this interface, use the interface of the superclass Term and construct 
 * instances only via
 * a TermFactory instead.
 */
class SubstitutionTerm extends Term {

    /** 
     * variable to substitute
     */
    private final ArrayOfQuantifiableVariable substVar;
    
    /** 
     * The two sub terms of the substitution term, where subs[0] is the term
     * with which the variable is substituted and subs[1] is the term on
     * which the substitution is applied. 
     * <code> {x/subs[0]}subs[1]</code>
     */
    private final ArrayOfTerm subs;

    /** depth of the term */
    private final int depth;
    

    /** creates a substitution term
     * @param op the Operator representing a substitution
     * @param substVar the Variable to be substituted
     * @param subs the Term that replaces substVar
     */
    public SubstitutionTerm(Operator op, 
			    QuantifiableVariable substVar, 
			    Term[] subs) {
	super(op, op.sort(subs));
	
	this.subs = new ArrayOfTerm(subs);
	this.substVar  = new ArrayOfQuantifiableVariable
	    (new QuantifiableVariable[] {substVar});
	this.depth = 1+(subs[0].depth() > subs[1].depth() ? 
			subs[0].depth() : subs[1].depth());
    }

    /**
     * returns the <code>n-th</code> subterm  
     * @return n-th subterm ( e.g. {x s} t (0:s ,  1: t) 
     */    
    public Term sub(int n) {
	return subs.getTerm(n);
    }	

    /**
     * returns the longest path from the root to the leaves
     * @return depth of the term 
     */
    public int depth() {
	return depth;
    }
   
    /**
     * returns <code>2<code> as arity of a substitution term 
     * @return arity of the substitution term 1 as int 
     */
    public int arity() {
	return 2;
    } 

    /**
     * the substitution term bound the substituted variable in second 
     * (attention: i.e. <code>n=1<code>) subterm
     * @return the bound variables of the n-th subterm 
     */
    public ArrayOfQuantifiableVariable varsBoundHere(int n) {
	return (n==0 ? EMPTY_VAR_LIST : substVar);
    }

}
