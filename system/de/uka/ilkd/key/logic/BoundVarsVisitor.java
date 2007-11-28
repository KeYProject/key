// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.op.SetAsListOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.SetOfQuantifiableVariable;

/** 
 * Visitor traversing a term and collecting all variables that occur bound.
 * The visitor implements also a continuation on sequents, traversing all of
 * the formulas occuring in the sequent.
 */
public class BoundVarsVisitor extends Visitor{
  
    private SetOfQuantifiableVariable bdVars =
	SetAsListOfQuantifiableVariable.EMPTY_SET;  

 
    /**
     * creates a Visitor that collects all bound variables for the subterms
     * of the term it is called from.
     */
    public BoundVarsVisitor() {
    }

    /**
     * only called by execPostOrder in Term.
     */
    public void visit(Term visited) {        
        for (int i = 0, ar = visited.arity(); i<ar; i++) {
            for (int j = 0, boundVarsSize = 
                visited.varsBoundHere(i).size(); j<boundVarsSize; j++) {
                bdVars=bdVars.add(visited.varsBoundHere(i)
                        .getQuantifiableVariable(j));	    
            }	  
        }
    }
    
    /**
     * visits a sequent
     */
    public void visit(Sequent visited) {        
        final IteratorOfConstrainedFormula it = visited.iterator();
        while (it.hasNext()) {
            visit(it.next().formula());            
        }        
    }
    
    /**
     * returns all the bound variables that have been stored
     */
    public SetOfQuantifiableVariable getBoundVariables(){
	return bdVars;
    }

}
