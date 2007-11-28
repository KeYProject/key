// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
