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
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a context is affected by the strictfp modifier
 */
public final class InStrictFp extends VariableConditionAdapter {

    private final boolean negated;

    public InStrictFp(boolean negation) {
        this.negated = negation;
    }
    
    public boolean isNegated(){
	return negated;
    }
    
    @Override
    public boolean check(SchemaVariable var, 
			 SVSubstitute instCandidate,
			 SVInstantiations instMap, 
			 Services services) {

	ExecutionContext ec = instMap.getExecutionContext();

	if (ec == null) {
	    return negated;
	} else {
	    IProgramMethod methodContext = ec.getMethodContext();
	    boolean strictfpClass = true;

	    try {
		Type t = ec.getTypeReference().getKeYJavaType().getJavaType();
		if (t instanceof ClassDeclaration) {
		    strictfpClass = ((ClassDeclaration)t).isStrictFp();
		} else {
		    strictfpClass = false;
		}
	    } catch (NullPointerException e) {
		    strictfpClass = false;
	    }
	    
	    final boolean isInStrictFp = strictfpClass ||
					 methodContext.isStrictFp();
	    return negated ? !isInStrictFp : isInStrictFp;
	}
    }
    
    
    @Override
    public String toString() {      
        String prefix = negated ? "\\not" : "";
	return prefix + "\\isStrictFp";
    }
}
