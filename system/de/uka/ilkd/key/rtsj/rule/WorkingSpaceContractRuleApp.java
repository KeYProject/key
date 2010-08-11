// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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
