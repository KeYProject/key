// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;


/**
 * Represents an application of a contract rule. Currently, this is only 
 * used for applications read in from a proof file; fresh applications are 
 * represented as regular BuiltInRuleApps. (yes, I know that this is ugly - BW) 
 */
public class ContractRuleApp extends AbstractContractRuleApp {

    private List<LocationVariable> heapContext;

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

    public boolean isSufficientlyComplete() {
        return pio != null;      
    }
    
    @Override
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
	if (contracts.size() !=1) return this; // incomplete app;
	Modality m = (Modality)programTerm().op();
	boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
	heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
	return setContract(contracts.iterator().next());
    }

    @Override
    public ContractRuleApp forceInstantiate(Goal goal) {
	if (complete()) {
		return this;
	}
	Services services = goal.proof().getServices();
	ImmutableSet<FunctionalOperationContract> contracts = UseOperationContractRule
	.getApplicableContracts(
			UseOperationContractRule.computeInstantiation(
					posInOccurrence().subTerm(), services),
					services);
	Modality m = (Modality)programTerm().op();
	boolean transaction = (m == Modality.DIA_TRANSACTION || m == Modality.BOX_TRANSACTION);
	heapContext = HeapContext.getModHeaps(goal.proof().getServices(), transaction);
	final FunctionalOperationContract combinedContract = services.getSpecificationRepository()
	.combineOperationContracts(contracts);
	return setContract(combinedContract);
    }

    @Override
    public ContractRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        super.setMutable(ifInsts);
        return this;
    }

    @Override
    public List<LocationVariable> getHeapContext() {
      return heapContext;
    }

    public Term programTerm() {
        if (posInOccurrence() != null) {
            return TermBuilder.DF.goBelowUpdates(posInOccurrence().subTerm());
        }
        return null;
    }

}
