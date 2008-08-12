package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.TypeDeclaration;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This variable condition checks if a given type denotes an interface type.
 */
public class InterfaceType extends VariableConditionAdapter {

    private final TypeResolver resolver;
    private final boolean negated;

    public InterfaceType(TypeResolver tr, boolean negation) {
        this.resolver = tr;
        this.negated = negation;
    }
    
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {
        final Sort sort = 
            resolver.resolveSort(var, instCandidate, instMap, services);
        final boolean isClassType  =  sort instanceof ClassInstanceSort;
        
        KeYJavaType kjt = services.getJavaInfo().getKeYJavaType(sort);
        if(kjt==null) kjt = services.getJavaInfo().getKeYJavaType(sort.toString());
        boolean b = true;
        if(kjt.getJavaType() instanceof TypeDeclaration){
            b = ((TypeDeclaration) kjt.getJavaType()).isInterface();
        }
        final boolean isInterface = !(sort instanceof ArraySort) && isClassType && b;
            
        return negated ? !isInterface : isInterface;
    }
    
    public String toString() {      
        String prefix = negated ? "\\not" : "";
        return prefix+"\\isInterface (" + resolver + ")";
    }
    
}
