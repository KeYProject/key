// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.BoundVariableTools;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.util.Debug;

/** 
 * Represents a pair of an update operator and the term
 * that is used to update the variable(attribute) of update operator.
 * 
 * The equals method implements equals mod renaming but with a strict sort
 * restriction.
 */
public class UpdatePair {

    /** the update terms */
    private final Term update;
    
    public UpdatePair(Term update) {
	//	super(update.op(), Sort.FORMULA);
        Debug.assertTrue(update.op() instanceof IUpdateOperator, 
			 "updatepair:: simultaneous update expected");	
	this.update = update;	
    }
    
    public int arity() {
	return update.arity() - 1;
    }
    
    public Term sub(int n) {
	if (n>=arity()) {
	    throw new IndexOutOfBoundsException();
	}
	return update.sub(n);
    }
    
    public ArrayOfQuantifiableVariable varsBoundHere (int n) {
        if ( n >= arity () ) throw new IndexOutOfBoundsException ();
        return update.varsBoundHere ( n );
    }
    
    public IUpdateOperator updateOperator() {
	return (IUpdateOperator)update.op();
    }

    /** 
     * equals modulo renaming of bound variables
     */
    public boolean equals(Object o) {
	if (!(o instanceof UpdatePair)) {
	    return false;
	}
	final UpdatePair cmp = (UpdatePair) o;	

	if (cmp.updateOperator() != updateOperator()) {
	    return false;
	}		

        
	for (int i = 0, ar = arity(); i<ar; i++) {        
	    final ArrayOfQuantifiableVariable qVars = varsBoundHere(i);
	    final ArrayOfQuantifiableVariable cmpQVars = cmp.varsBoundHere(i);
	    if (qVars.size() != cmpQVars.size()) {
		return false;
	    } else if (qVars.size() == 0) {
		if (!sub(i).equals(cmp.sub(i))) {
		    return false;
		} 
	    } else {	    
		if (!BoundVariableTools.DEFAULT.
		    equalsModRenaming(qVars, sub(i), cmpQVars, cmp.sub(i))) {
		    return false;
		}
	    }
	}
	return true;
    }
    
    public int hashCode(){
    	int result = 17;
    	result = 37 * result;
    	return result;
    }

    public String toString() {
	return "{pair:" + update.toString() + "}";
    }
    
}
