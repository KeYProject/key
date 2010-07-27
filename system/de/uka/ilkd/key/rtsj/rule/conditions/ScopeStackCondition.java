package de.uka.ilkd.key.rtsj.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rtsj.java.RTSJInfo;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class ScopeStackCondition extends VariableConditionAdapter {

    private SchemaVariable var;
    private boolean neg;

    /**
     * @param var the SchemaVariable to be checked
     */
    public ScopeStackCondition(SchemaVariable var, boolean neg) {
        this.var = var; 
        this.neg = neg;
    }
    
    public boolean check(SchemaVariable var, 
                 SVSubstitute candidate, 
                 SVInstantiations svInst,
                 Services services) {
        if(var!=this.var) return true;
        ProgramVariable pv;
        if (candidate instanceof FieldReference) {
            pv = ((FieldReference)candidate).getProgramVariable();
        }else if(candidate instanceof ProgramVariable){
            pv = (ProgramVariable) candidate;
        }else{
            return true;
        }
        boolean result = (pv.name().toString().indexOf(("stack"))!=-1);
        if(pv.getContainerType()!=null && result){
            result = pv.getContainerType().getSort().extendsTrans(
                    ((RTSJInfo) services.getJavaInfo()).getJavaxRealtimeMemoryArea().getSort());
        }else{
            return true;
        }
        return neg^result;
    }
    
    public String toString () {
        return (neg ? "\\not " : "") + "\\stack(" + var + ")";
    }
    
}


