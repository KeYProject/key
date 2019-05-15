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
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class ArrayLengthCondition extends VariableConditionAdapter {

    private final SchemaVariable reference;
    private final boolean negation;


    public ArrayLengthCondition(SchemaVariable reference, boolean negation) {
	this.reference = reference;
	this.negation  = negation;
    }


    @Override
    public boolean check(SchemaVariable var, 
			 SVSubstitute subst, 
			 SVInstantiations svInst,
			 Services services) {
	if(var == reference) {
	    ProgramVariable attribute;
	    if(subst instanceof FieldReference) {
		attribute = ((FieldReference)subst).getProgramVariable();
	    } else {
		attribute = (ProgramVariable)subst;
	    }
	    return negation 
	           ^ attribute == services.getJavaInfo().getArrayLength();
	}
	return true;
    }

    
    @Override
    public String toString () {
	return (negation ? " \\not " : "" ) + "\\isArrayLength(" + reference + ")";
    }
}