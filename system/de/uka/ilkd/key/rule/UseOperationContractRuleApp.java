// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;


/**
 * Represents an application of the use contract rule. Currently, this is only 
 * used for applications read in from a proof file; fresh applications are 
 * represented as regular BuiltInRuleApps. (yes, I know that this is ugly - BW) 
 */
public class UseOperationContractRuleApp extends BuiltInRuleApp {

    private final ContractWithInvs instantiation;
    
    public UseOperationContractRuleApp(BuiltInRule contractRule,
	    			       PosInOccurrence pio,
                                       Constraint userConstraint,
                                       ContractWithInvs instantiation) {
        super(contractRule, pio, userConstraint);
        this.instantiation = instantiation;
    }   
    
    public ContractWithInvs getInstantiation() {
        return instantiation;
    }
}
