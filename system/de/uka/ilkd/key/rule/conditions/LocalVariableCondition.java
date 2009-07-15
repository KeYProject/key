// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 *  Ensures the given ProgramElement denotes a local variable
 */
public class LocalVariableCondition extends VariableConditionAdapter {

    private SchemaVariable var;
    private boolean neg;
    
    public LocalVariableCondition(SchemaVariable var, boolean neg) {
        this.var = var;
        this.neg = neg;
	if (!(var instanceof ProgramSV)) {   
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
        final boolean isLocalVar = ((candidate instanceof ProgramVariable) &&  
                !((ProgramVariable)candidate).isMember());
        return neg ? !isLocalVar : isLocalVar;
    }

    public String toString () {
        return "\\isLocalVariable (" + var+ ")";
    }

}
