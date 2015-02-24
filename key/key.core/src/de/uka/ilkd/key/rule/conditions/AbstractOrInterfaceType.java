// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
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
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a given type denotes an abstract class or
 * interface type.
 */
public final class AbstractOrInterfaceType extends VariableConditionAdapter {

    private final TypeResolver resolver;
    private final boolean negated;

    public AbstractOrInterfaceType(TypeResolver tr, boolean negation) {
        this.resolver = tr;
        this.negated = negation;
    }
    
    public boolean isNegated(){
	return negated;
    }
    
    public TypeResolver getTypeResolver(){
	return resolver;
    }
    
    @Override
    public boolean check(SchemaVariable var, 
	    		 SVSubstitute instCandidate,
	    		 SVInstantiations instMap, 
	    		 Services services) {
        final Sort sort = 
            resolver.resolveSort(var, instCandidate, instMap, services);
                        
        final boolean isAbstractOrInterface = sort.isAbstract();
        
        return negated ? !isAbstractOrInterface : isAbstractOrInterface;
    }
    
    
    @Override
    public String toString() {      
        String prefix = negated ? "\\not" : "";
        return prefix+"\\isAbstractOrInterface (" + resolver + ")";
    }
}