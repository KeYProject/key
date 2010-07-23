package de.uka.ilkd.key.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rtsj.logic.op.WorkingSpaceRigidOp;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TestEqualWorkingSpaceOp extends VariableConditionAdapter {

    private SchemaVariable sv1, sv2;
    
    public TestEqualWorkingSpaceOp(SchemaVariable sv1, SchemaVariable sv2){
        this.sv1 = sv1;
        this.sv2 = sv2;
    }
    
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {
        Term ws1 = (Term) instMap.getInstantiation(sv1);
        if(ws1 == null || !(ws1.op() instanceof WorkingSpaceRigidOp)) return false;
        Term ws2 = (Term) instMap.getInstantiation(sv2);
        return ws2 != null && ((IWorkingSpaceOp) ws1.op()).getProgramMethod().
        equals(((IWorkingSpaceOp) ws2.op()).getProgramMethod());
    }
    
    public String toString(){
        return "\\equalWorkingSpaceOp("+sv1+"," +sv2+")";
    }

}
