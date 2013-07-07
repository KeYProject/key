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
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


/**
 * This variable condition checks if a given type denotes an abstract class or
 * interface type.
 */
public final class IsThisReference extends VariableConditionAdapter {

    private final boolean negated;
    private final ParsableVariable var;

    public IsThisReference(ParsableVariable var, boolean negation) {
        this.negated = negation;
        this.var = var;
        assert var.sort() == ProgramSVSort.VARIABLE;
    }
    

    public boolean isNegated(){
	return negated;
    }

      
    @Override
    public boolean check(SchemaVariable var, 
	    		 SVSubstitute instCandidate,
	    		 SVInstantiations instMap, 
	    		 Services services) {
        if(var != this.var) {
          return true;
        }
//        boolean isThisRef = instMap.getInstantiation(var) instanceof ThisReference;
        boolean isThisRef = instCandidate instanceof ThisReference;
        return negated ? !isThisRef : isThisRef;
    }
    
    
    @Override
    public String toString() {      
        String prefix = negated ? "\\not" : "";
        return prefix+"\\isThisReference (" + var + ")";
    }
}
