// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 *  Ensures the given ProgramElement denotes a local variable
 */
public class IsUpdatedVariableCondition extends VariableConditionAdapter {
    private SchemaVariable var;

    public IsUpdatedVariableCondition(SchemaVariable var) {
        this.var = var;
        if (!(var.isFormulaSV() || var.isTermSV() )) {
            throw new IllegalArgumentException("Illegal schema variable");
        }
    }	
    /**
     * checks if the condition for a correct instantiation is fulfilled
     * @param var the template Variable to be instantiated
     * @param candidate the SVSubstitute which is a candidate for an
     * instantiation of var
     * @param svInst the SVInstantiations that are already known to be needed 
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable var, 
            SVSubstitute candidate, 
            SVInstantiations svInst,
            Services services) {
        if (var != this.var) { 
            return true; 
        }
        if(candidate==null)
            return false;
        if (!(candidate instanceof Term)){
//          System.out.println("Candidate is not a term");
//          System.out.println("Candidate="+candidate.toString());
            return false; 
        }
        Term term = (Term)candidate;
//      System.out.println("Candidate:"+term.toString());
        return term.op() instanceof IUpdateOperator;
    }
    public String toString () {
        return "\\isUpdated (" + var+ ")";
    }

}
