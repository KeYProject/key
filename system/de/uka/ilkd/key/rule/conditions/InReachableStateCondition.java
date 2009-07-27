// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This conditions checks if the update prefix is empty
 * and that the instantiation of the sv is the predicate 
 * <tt>inReachableState</tt> maybe preceeded by one Update
 */
public final class InReachableStateCondition extends VariableConditionAdapter {

    private final SchemaVariable inReachableState;
    
    public InReachableStateCondition(SchemaVariable sv) {
        inReachableState = sv;
    }
    
    
    @Override
    public boolean check(SchemaVariable var, 
	    		 SVSubstitute subst,
	    		 SVInstantiations svInst, 
	    		 Services services) {

        if (var != inReachableState) return true;
        
        if (!(subst instanceof Term)) return false;
        
        Term t = (Term)subst;        

        if (t.op() instanceof UpdateApplication) {
            t = UpdateApplication.getTarget(t);
        } else {
            // would otherwise return inReachableState, not wrong but useless
           return false;
        }
                
        return t.op() == services.getTypeConverter().getHeapLDT().getWellFormed() && 
          svInst.getUpdateContext().isEmpty();
    }

    
    @Override
    public String toString() {
        return "\\isInReachableState(" + inReachableState + ")";
    }
}
