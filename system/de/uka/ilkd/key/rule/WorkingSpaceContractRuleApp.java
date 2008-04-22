package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.gui.WorkingSpaceContractDialog;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

public class WorkingSpaceContractRuleApp extends BuiltInRuleApp {

    public WorkingSpaceContractRuleApp(PosInOccurrence pio,
                                 Constraint userConstraint) {
        super(UseWorkingSpaceContractRule.INSTANCE, pio, userConstraint);
    }   
    
}