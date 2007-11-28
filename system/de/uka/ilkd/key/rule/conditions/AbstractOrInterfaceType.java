// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.ClassType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
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
        final KeYJavaType type = 
            resolver.resolveType(var, instCandidate, instMap, services);
        
        final boolean isClassType  =  type.getJavaType() instanceof ClassType;
        
        final boolean isAbstractOrInterface = isClassType && 
            ((ClassType)type.getJavaType()).isInterface() ||
            ((ClassType)type.getJavaType()).isAbstract();
        
        return negated ? !isAbstractOrInterface : isAbstractOrInterface;
    }
    
    public String toString() {      
        String prefix = negated ? "\\not" : "";
        return prefix+"\\isAbstractOrInterface (" + resolver + ")";
    }

}
