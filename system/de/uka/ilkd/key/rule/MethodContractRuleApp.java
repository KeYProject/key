package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.mgt.OldOperationContract;

public class MethodContractRuleApp extends BuiltInRuleApp {

    private OldOperationContract contract;
    
    public MethodContractRuleApp(UseMethodContractRule builtInRule, 
                                 PosInOccurrence pio,
                                 Constraint userConstraint,
                                 OldOperationContract contract) {
        super(builtInRule, pio, userConstraint);
        this.contract = contract;
    }   
    
    public OldOperationContract getMethodContract() {
        return contract;
    }

    
}
