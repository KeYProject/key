package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class NoMemoryAreaCondition extends VariableConditionAdapter {

    private SchemaVariable var;

    /**
     * creates an instance of this condition checking if var has reference type
     * @param var the SchemaVariable to be checked
     */
    public NoMemoryAreaCondition(SchemaVariable var) {
        this.var = var; 
    }
    
    public boolean check(SchemaVariable var, 
                 SVSubstitute candidate, 
                 SVInstantiations svInst,
                 Services services) {
        if(var!=this.var) return true;
        if(!(candidate instanceof Term)) return true;
        Sort s = ((Term) candidate).sort();
        return !s.extendsTrans(services.getJavaInfo().getJavaxRealtimeMemoryArea().getSort());
    }
    
}
