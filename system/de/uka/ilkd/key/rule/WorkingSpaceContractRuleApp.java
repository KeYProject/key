package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;

public class WorkingSpaceContractRuleApp extends BuiltInRuleApp {

    public WorkingSpaceContractRuleApp(PosInOccurrence pio,
                                 Constraint userConstraint) {
        super(UseWorkingSpaceContractRule.INSTANCE, pio, userConstraint);
    }   
    
}