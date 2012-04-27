// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;


/**
 * Represents an application of a contract rule. Currently, this is only 
 * used for applications read in from a proof file; fresh applications are 
 * represented as regular BuiltInRuleApps. (yes, I know that this is ugly - BW) 
 */
public class ContractRuleApp extends AbstractContractRuleApp {

    ContractRuleApp(BuiltInRule rule, PosInOccurrence pio) {
    	this(rule,	pio, null);
    }   

    private ContractRuleApp(BuiltInRule rule, 
    		PosInOccurrence pio, Contract instantiation) {
    	super(rule, pio, instantiation);
    }
    
    public ContractRuleApp(BuiltInRule rule, PosInOccurrence pio,
            ImmutableList<PosInOccurrence> ifInsts, Contract instantiation) {
        super(rule, pio, ifInsts, instantiation);
    }

    public ContractRuleApp replacePos(PosInOccurrence newPos) {
	    return new ContractRuleApp(rule(), newPos, instantiation);
    }
    
    public ContractRuleApp setContract(Contract contract) {
        return new ContractRuleApp(rule(), posInOccurrence(), contract);
    }
    
    public UseOperationContractRule rule() {
    	return (UseOperationContractRule) super.rule();
    }

    public ContractRuleApp tryToInstantiate(Goal goal) {
    	if (complete()) {
    		return this;
    	}
    	Services services = goal.proof().getServices();
    	ImmutableSet<FunctionalOperationContract> contracts = UseOperationContractRule
    	        .getApplicableContracts(
    	                UseOperationContractRule.computeInstantiation(
    	                        posInOccurrence().subTerm(), services),
    	                services);
    	return setContract(services.getSpecificationRepository()
    	                .combineOperationContracts(
    	                		contracts));
    }

    @Override
    public ContractRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        return new ContractRuleApp(builtInRule, pio, ifInsts, instantiation);
    }

}
