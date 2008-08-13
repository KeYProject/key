package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class MemoryAreaCondition extends VariableConditionAdapter {

    private SchemaVariable var;
    private boolean neg;

    /**
     * creates an instance of this condition checking if var has reference type
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
            return neg^s.extendsTrans(services.getJavaInfo().getJavaxRealtimeMemoryArea().getSort());
        }else if(candidate instanceof ProgramVariable){
            return neg^(((ProgramVariable) candidate).name().toString().indexOf((ImplicitFieldAdder.IMPLICIT_MEMORY_AREA))!=-1);
        }
        return false;        
    }
    
}
