package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;

public class WorkingSpaceContractRuleApp extends BuiltInRuleApp {

    private OperationContract spec;
    /**
     * -1 iff the precondition of spec is supposed to be weaker than the 
     * precondition associated with the selected working_space term.
     * 0 iff equivalent
     * 1 iff stronger
     */
    private int compare;
    
    public WorkingSpaceContractRuleApp(PosInOccurrence pio,
                                 Constraint userConstraint,
                                 OperationContract spec,
                                 int compare) {
        super(UseWorkingSpaceContractRule.INSTANCE, pio, userConstraint);
        this.spec = spec;
        this.compare = compare;
    }   
    
    public OperationContract getOperationContract() {
        return spec;
    }
    
    public int compare(){
        return compare;
    }

    
}