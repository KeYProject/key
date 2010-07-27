package de.uka.ilkd.key.rtsj.rule.conditions;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rtsj.logic.op.WorkingSpaceNonRigidOp;
import de.uka.ilkd.key.rtsj.logic.op.WorkingSpaceRigidOp;
import de.uka.ilkd.key.rule.VariableConditionAdapter;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class TestWorkingSpaceOp extends VariableConditionAdapter {

    private SchemaVariable sv1;
    
    public TestWorkingSpaceOp(SchemaVariable sv1){
        this.sv1 = sv1;
    }
    
    public boolean check(SchemaVariable var, SVSubstitute instCandidate,
            SVInstantiations instMap, Services services) {
        if(sv1!=var) return true;
        Term ws1 = (Term) instMap.getInstantiation(sv1);
        if(ws1==null){
            return false;
        }
        while(ws1.op() instanceof IUpdateOperator){
            ws1 = ((IUpdateOperator) ws1.op()).target(ws1);
        }
        return ws1.op() instanceof WorkingSpaceRigidOp || ws1.op() instanceof WorkingSpaceNonRigidOp;
    }
    
    public String toString(){
        return "\\testWorkingSpaceOp("+sv1+")";
    }
    
}
