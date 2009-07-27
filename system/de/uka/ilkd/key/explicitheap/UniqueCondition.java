// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.explicitheap;


import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;


public final class UniqueCondition extends VariableConditionAdapter {
    
    private final SchemaVariable var;
    
    
    public UniqueCondition(SchemaVariable var) {
        this.var = var;
    }

    
    @Override
    public boolean check(SchemaVariable var, 
                         SVSubstitute candidate, 
                         SVInstantiations svInst,
                         Services services) {
        if (var != this.var) { 
            return true; 
        } else if(!(candidate instanceof Term)) {
            return false;
        } else {
            Term candTerm = (Term)candidate;
            return candTerm.op() instanceof Function
                   && ((Function)candTerm.op()).isUnique();
        }
    }
    

    @Override
    public String toString () {
        return "\\isUnique (" + var+ ")";
    }
}
