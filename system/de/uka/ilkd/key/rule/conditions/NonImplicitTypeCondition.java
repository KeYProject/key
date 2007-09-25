// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 *  This variable condition checks if a schemavariable is instantiated with a reference type
 */
public class NonImplicitTypeCondition extends VariableConditionAdapter {

    private SchemaVariable var;

    /**
     * creates an instance of this condition checking if var has reference type
     * @param var the SchemaVariable to be checked
     */
    public NonImplicitTypeCondition(SchemaVariable var) {
	this.var = var;	
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
        if (var != this.var) return true;
	return !((candidate instanceof ProgramVariable) && 
		 ((ProgramVariable) candidate).isImplicit());
    }

    public String toString () {
	return "\\isNonImplicit(" + var + ")";
    }

}
