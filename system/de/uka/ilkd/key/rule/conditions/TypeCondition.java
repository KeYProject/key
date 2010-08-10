// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 *  This variable condition checks if a schemavariable is instantiated 
 *  with a reference or primitive type
 */
public class TypeCondition extends VariableConditionAdapter {

    private final TypeResolver resolver;
   
    private final boolean nonNull;

    private final boolean isReference;

    /**
     * create a type condition     
     * @param tr the TypeResolver for the type to be checked
     * @param isReference check for reference or primitive type  
     * @param nonNull if Sort null should be allowed (only important when 
     * isReference is set to true)
     */
    public TypeCondition(TypeResolver tr, boolean isReference, boolean nonNull) {
        this.resolver = tr;
        this.isReference = isReference;
        this.nonNull = nonNull;
    }
    
    /**
     * checks if the condition for a correct instantiation is fulfilled
     * @param p_var the template Variable to be instantiated
     * @param candidate the SVSubstitute which is a candidate for an
     * instantiation of var
     * @param svInst the SVInstantiations that are already known to be needed 
     * @return true iff condition is fulfilled
     */
    public boolean check(SchemaVariable p_var, 
			 SVSubstitute candidate, 
			 SVInstantiations svInst,
			 Services services) {
        
        if (!resolver.isComplete(p_var, candidate, svInst, services)) {
            // instantiation not yet complete
            return true;
        }
        final Sort s = resolver.resolveSort(p_var, candidate, svInst, services);
        
        if (isReference) {        
            return (s instanceof ObjectSort && (!nonNull || s != Sort.NULL));
        } else {
            return !(s instanceof ObjectSort);
        }
    }

    public String toString () {
        String prefix = "\\isReference";
        if (isReference && nonNull) {
            prefix += "[non_null]";
        }               
        return (isReference ? "" : "\\not" ) + prefix + "( " + resolver + " )";            
    }
    
    /** 
     * @return returns value of <code>isReference</code>.
     */
    public boolean getIsReference() {return isReference;}
    
    /** 
     * @return returns value of <code>nonNull</code>.
     */
    public boolean getNonNull() {return nonNull;}
    /**
     * @return returns value of <code>resolver</code>.
     */
    public TypeResolver getTypeResolver() {return resolver;}

}
