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
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * Ensures the given ProgramElement denotes a local variable
 */
public final class LocalVariableCondition extends VariableConditionAdapter {

    private final SchemaVariable var;
    private final boolean neg;
    
    public LocalVariableCondition(SchemaVariable var, boolean neg) {
        this.var = var;
        this.neg = neg;
	if (!(var instanceof ProgramSV)) {   
            throw new IllegalArgumentException("Illegal schema variable");
        }
    }

    
    @Override    
    public boolean check(SchemaVariable var, 
            		 SVSubstitute candidate, 
            		 SVInstantiations svInst,
            		 Services services) {

        if (var != this.var) { 
            return true; 
        }
        final boolean isLocalVar = ((candidate instanceof ProgramVariable) &&  
                !((ProgramVariable)candidate).isMember());
        return neg ? !isLocalVar : isLocalVar;
    }

    
    @Override
    public String toString () {
        return "\\isLocalVariable (" + var+ ")";
    }
}
