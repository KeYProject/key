// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.conditions;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 *  This variable condition checks if a schemavariable is instantiated 
 *  with a reference or primitive type
 */
public final class TypeCondition extends VariableConditionAdapter {

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
    
    public TypeResolver getResolver(){
	return resolver;
    }
    
    public boolean getIsReference(){
	return isReference;
    }
    
    public boolean getNonNull(){
	return nonNull;
    }
    
    
    @Override
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
            return (s.extendsTrans(services.getJavaInfo().objectSort()) 
        	    && !(nonNull && s instanceof NullSort));
        } else {
            return !(s.extendsTrans(services.getJavaInfo().objectSort()));
        }
    }

    
    @Override
    public String toString () {
        String prefix = "\\isReference";
        if (isReference && nonNull) {
            prefix += "[non_null]";
        }               
        return (isReference ? "" : "\\not" ) + prefix + "( " + resolver + " )";            
    }
    

    /**
     * @return returns value of <code>resolver</code>.
     */
    public TypeResolver getTypeResolver() {return resolver;}
}
