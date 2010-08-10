// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rtsj.java.RTSJInfo;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class MemoryAreaCondition extends VariableConditionAdapter {

    private SchemaVariable var;
    private boolean neg;

    /**
     * @param var the SchemaVariable to be checked
     */
    public MemoryAreaCondition(SchemaVariable var, boolean neg) {
        this.var = var; 
        this.neg = neg;
    }
    
    public boolean check(SchemaVariable var, 
                 SVSubstitute candidate, 
                 SVInstantiations svInst,
                 Services services) {
        if(var!=this.var) return true;
        Sort s;
        if(candidate instanceof Term){
            s = ((Term) candidate).sort();
            return neg^s.extendsTrans(((RTSJInfo) services.getJavaInfo()).getJavaxRealtimeMemoryArea().getSort());
        }else if(candidate instanceof ProgramVariable){
            return neg^(((ProgramVariable) candidate).name().toString().indexOf((ImplicitFieldAdder.IMPLICIT_MEMORY_AREA))!=-1);
        }
        return true;        
    }
    
    public String toString () {
        return (neg ? "\\not " : "") + "\\memoryArea(" + var + ")";
    }
    
}
