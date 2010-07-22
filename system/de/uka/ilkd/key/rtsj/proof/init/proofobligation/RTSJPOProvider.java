package de.uka.ilkd.key.rtsj.proof.init.proofobligation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.proofobligation.DefaultPOProvider;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

public class RTSJPOProvider extends DefaultPOProvider {

    public static final String RESPECTS_WORKING_SPACE = "RespectsWorkingSpace";
    private final boolean memoryConsumptionAware;

    public RTSJPOProvider(boolean memory) {
	memoryConsumptionAware = memory;
    }

    public ImmutableList<String> getPOsFor(SpecificationRepository specRepos,
	    ProgramMethod pm) {
	ImmutableList<String> pos = super.getPOsFor(specRepos, pm);

	if (specRepos.getOperationContracts(pm).size() > 0
	        && memoryConsumptionAware) {
	    pos = pos.append(RESPECTS_WORKING_SPACE);
	}
	
	return pos;
    }
    
    public ProofOblInput createRespectsWorkingSpacePO(InitConfig initConfig,
	    OperationContract contract, ImmutableSet<ClassInvariant> assumedInvs) {
	return new RespectsWorkingSpacePO(initConfig, contract, assumedInvs);
    }

    public ImmutableList<ProofOblInput> getRequiredCorrectnessProofsFor(
	    OperationContract atomicContract, ContractWithInvs cwi,
	    InitConfig initConfig) {

	ImmutableList<ProofOblInput> pos = ImmutableSLList
	        .<ProofOblInput> nil();

	if (memoryConsumptionAware) {
	    pos = pos.prepend(createRespectsModifiesPO(initConfig,
		    atomicContract, cwi.assumedInvs()));
	}

	return pos.prepend(super.getRequiredCorrectnessProofsFor(
	        atomicContract, cwi, initConfig));
    }
    
    public ImmutableList<String> getRequiredCorrectnessProofObligationsForOperationContracts() {
	ImmutableList<String> requiredOperationCorrectnessPOs = 
	    super.getRequiredCorrectnessProofObligationsForOperationContracts();

	if (memoryConsumptionAware) {
	    requiredOperationCorrectnessPOs = 
		requiredOperationCorrectnessPOs.append(RESPECTS_WORKING_SPACE);
	}
	
	return requiredOperationCorrectnessPOs;
    }

    public ProofOblInput createOperationContractPOByName(String poName,
	    ContractWithInvs cwi, InitConfig initConfig) {
	if (RESPECTS_WORKING_SPACE.equals(poName)) {
	    return createRespectsWorkingSpacePO(initConfig, cwi.contract(), cwi.assumedInvs());
	} else {
	    return super.createOperationContractPOByName(poName, cwi, initConfig);
	}
    }
}
