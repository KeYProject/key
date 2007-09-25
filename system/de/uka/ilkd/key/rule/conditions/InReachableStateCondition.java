package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.IUpdateOperator;
import de.uka.ilkd.key.logic.op.SVSubstitute;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * This conditions checks if the update prefix is empty
 * and that the instantiation of the sv is the predicate 
 * <tt>inReachableState</tt> maybe proceeded by one Update
 */
public class InReachableStateCondition extends VariableConditionAdapter {

    final private SchemaVariable inReachableState;
    
    public InReachableStateCondition(SchemaVariable sv) {
        inReachableState = sv;
    }
    
    
    /**
     * true if the predicate <tt>inReachableState</tt> is preceeded by one or 
     * no updates
     */
    public boolean check(SchemaVariable var, SVSubstitute subst,
            SVInstantiations svInst, Services services) {

        if (var != inReachableState) return true;
        
        if (!(subst instanceof Term)) return false;
        
        Term t = (Term)subst;        

        if (t.op() instanceof IUpdateOperator && 
                !(t.op() instanceof AnonymousUpdate)) {
            t = ((IUpdateOperator)t.op()).target(t);
        } else {
            // would otherwise return inReachableState, not wrong but useless
           return false;
        }
                
        return t.op() == services.getJavaInfo().getInReachableState() && 
          svInst.getUpdateContext().isEmpty();
    }

    public String toString() {
        return "\\isInReachableState(" + inReachableState + ")";
    }
    
}
