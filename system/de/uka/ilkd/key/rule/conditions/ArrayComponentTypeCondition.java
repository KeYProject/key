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


import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 *  This variable condition checks if an array component is of reference type
 */
public class ArrayComponentTypeCondition extends VariableConditionAdapter {

    private SchemaVariable var;
    private boolean checkReferenceType;

    /**
     * creates an instance of this condition checking if array var has reference
     * or primitive component type depending on the value of
     *  <code>checkReferenceType</code>
     * @param var the SchemaVariable to be checked
     * @param checkReferenceType the boolean flag which when is set (<tt>true</tt>) 
     * checks for reference otherwise for primitive type
     */
    public ArrayComponentTypeCondition(SchemaVariable var, 
            boolean checkReferenceType) {
	this.var = var;	
	this.checkReferenceType = checkReferenceType;
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
        Sort s = null;
	if (candidate instanceof Term) {
	    s = ((Term)candidate).sort();
	} else if (candidate instanceof Expression) {
	    s = ((Expression)candidate).getKeYJavaType(services, 
	            svInst.getExecutionContext()).getSort();
	} else if (candidate instanceof TypeReference) {
	    s = ((TypeReference)candidate).getKeYJavaType().getSort();
	}
        
	if (s==null || !(s instanceof ArraySort)) {
	    return false;
	}
	return !(((ArraySort)s).elementSort() instanceof ObjectSort) ^ checkReferenceType;
    }

    public String toString () {
	return ( checkReferenceType ? "" : " \\not " ) + 
	  "\\isReferenceArray(" + var + ")";
    }

}
