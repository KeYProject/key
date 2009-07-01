// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.*;

/**
 * This class is used to collect all appearing variables that can
 * represent logic variables in a term. Duplicates are not removed
 * because the use of persistent datastructure and up to now we just 
 * have a SetAsList-implementation causing to 
 * have O(sqr(n)) if it would used.
 */
public class LVRCollector extends Visitor{
    /** collects all found variables */
    private ListOfQuantifiableVariable varList;

    /** creates the Variable collector */
    public LVRCollector() {
	varList = SLListOfQuantifiableVariable.EMPTY_LIST;
    }

    /** is called by the execPostOrder-method of a term 
     * @param t the Term to checked if it is a Variable and if true the
     * Variable is added to the list of found Variables
     */  
    public void visit(Term t) {
	if (t.op() instanceof QuantifiableVariable) {
	    varList=varList.prepend((QuantifiableVariable)t.op());
	} else if (t.op() instanceof Quantifier) {
	    for (int j = 0, ar = ((Quantifier)t.op()).arity(); j<ar; j++) {
	        for (int i = 0, sz = t.varsBoundHere(j).size(); i<sz;i++) {		
	            varList=varList.prepend
	            (t.varsBoundHere(j).getQuantifiableVariable(i));		
	        }
	    }
	}
    }

        
    /** @return iterator of the found Variables */
    public IteratorOfQuantifiableVariable varIterator() {
	return varList.iterator();
    }

    /** @return true iff term contains the given variable */
    public boolean contains(QuantifiableVariable var) {
	return varList.contains(var);
    }

}
