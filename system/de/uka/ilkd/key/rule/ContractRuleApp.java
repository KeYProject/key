// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.OperationContract;


/**
 * Represents an application of a contract rule. Currently, this is only 
 * used for applications read in from a proof file; fresh applications are 
 * represented as regular BuiltInRuleApps. (yes, I know that this is ugly - BW) 
 */
public class ContractRuleApp extends BuiltInRuleApp {

    private final Contract instantiation;
    
    public ContractRuleApp(PosInOccurrence pio,
	    		   Constraint userConstraint,
	    		   Contract instantiation) {
        super(instantiation instanceof OperationContract 
              ? UseOperationContractRule.INSTANCE
              : UseDependencyContractRule.INSTANCE,
              pio, 
              userConstraint);
        this.instantiation = instantiation;
    }   
    
    public Contract getInstantiation() {
        return instantiation;
    }
}
