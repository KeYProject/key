package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.ClassInstanceSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a given type denotes an abstract class or
 * interface type.
 */
public class AbstractOrInterfaceType extends VariableConditionAdapter {

    private final TypeResolver resolver;
    private final boolean negated;

    public AbstractOrInterfaceType(TypeResolver tr, boolean negation) {
        this.resolver = tr;
        this.negated = negation;
    }
    
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {
        final Sort sort = 
            resolver.resolveSort(var, instCandidate, instMap, services);
        
        final boolean isClassType  =  sort instanceof ClassInstanceSort;
                
        final boolean isAbstractOrInterface = 
            !(sort instanceof ArraySort) &&  
              (isClassType && ((ClassInstanceSort)sort).representAbstractClassOrInterface());
        
        return negated ? !isAbstractOrInterface : isAbstractOrInterface;
    }
    
    public String toString() {      
        String prefix = negated ? "\\not" : "";
        return prefix+"\\isAbstractOrInterface (" + resolver + ")";
    }

}
