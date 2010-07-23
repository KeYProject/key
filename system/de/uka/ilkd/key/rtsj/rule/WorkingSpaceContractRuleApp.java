package de.uka.ilkd.key.rtsj.rule;

import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.rule.BuiltInRuleApp;

public class WorkingSpaceContractRuleApp extends BuiltInRuleApp {

    public WorkingSpaceContractRuleApp(PosInOccurrence pio,
                                 Constraint userConstraint) {
        super(UseWorkingSpaceContractRule.INSTANCE, pio, userConstraint);
    }   
    
}