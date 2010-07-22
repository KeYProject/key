package de.uka.ilkd.key.proof.init.proofobligation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.ContractWithInvs;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

public class DefaultPOProvider implements POProvider {

    public static final String BEHAVIOURAL_SUBTYPING_INV = "BehaviouralSubtypingInv";
    public static final String PRESERVES_GUARD = "PreservesGuard";
    public static final String SPECIFICATION_EXTRACTION = "SpecificationExtraction";
    public static final String RESPECTS_MODIFIES = "RespectsModifies";
    public static final String ENSURES_POST = "EnsuresPost";
    public static final String PRESERVES_OWN_INV = "PreservesOwnInv";
    public static final String PRESERVES_INV = "PreservesInv";
    public static final String STRONG_OPERATION_CONTRACT = "StrongOperationContract";

    public ImmutableList<String> getPOsFor(SpecificationRepository specRepos,
	    ProgramMethod pm) {
	ImmutableList<String> pos = ImmutableSLList.<String> nil();

	/*
	 * //BehaviouralSubtypingOpPair
	 * if(specRepos.getOperationContracts(pm).size() > 0 &&
	 * javaInfo.getDirectSuperTypes(pm.getContainerType()).size() > 0) { pos
	 * = pos.append("BehaviouralSubtypingOpPair"); }
	 */

	// StrongOperationContract
	if (specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append(STRONG_OPERATION_CONTRACT);
	}

	// PreservesInv
	pos = pos.append(PRESERVES_INV);

	// PreservesOwnInv
	if (specRepos.getClassInvariants(pm.getContainerType()).size() > 0) {
	    pos = pos.append(PRESERVES_OWN_INV);
	}

	// EnsuresPost
	if (specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append(ENSURES_POST);
	}

	// RespectsModifies
	if (specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append(RESPECTS_MODIFIES);
	}

	// implemented by mbender for jmltest
	// Specification Extraction
	if (specRepos.getOperationContracts(pm).size() > 0) {
	    pos = pos.append(SPECIFICATION_EXTRACTION);
	}

	// PreservesGuard
	pos = pos.append(PRESERVES_GUARD);
	return pos;
    }

    public ImmutableList<String> getPOsFor(SpecificationRepository specRepos,
	    JavaInfo javaInfo, KeYJavaType kjt) {
	ImmutableList<String> pos = ImmutableSLList.<String> nil();

	// BehaviouralSubtypingInv
	if (specRepos.getClassInvariants(kjt).size() > 0
	        && javaInfo.getDirectSuperTypes(kjt).size() > 0) {
	    pos = pos.append(BEHAVIOURAL_SUBTYPING_INV);
	}

	return pos;
    }

    public ProofOblInput createStrongOperationContractPO(InitConfig initConfig,
	    OperationContract contract,
	    ImmutableSet<ClassInvariant> assumedInvs,
	    ImmutableSet<ClassInvariant> ensuredInvs) {
	return new StrongOperationContractPO(initConfig, contract, assumedInvs,
	        ensuredInvs);
    }

    public ProofOblInput createSpecExtPO(InitConfig initConfig,
	    OperationContract contract,
	    ImmutableSet<ClassInvariant> assumedInvs, ProgramMethod pm) {
	return new SpecExtPO(initConfig, contract, assumedInvs, pm);
    }

    public ProofOblInput createPreservesGuardPO(InitConfig initConfig,
	    ProgramMethod pm, ImmutableSet<ClassInvariant> guardedInvariants,
	    ImmutableSet<KeYJavaType> guard) {
	return new PreservesGuardPO(initConfig, pm, guardedInvariants, guard);
    }

    public ProofOblInput createRespectsModifiesPO(InitConfig initConfig,
	    OperationContract contract, ImmutableSet<ClassInvariant> assumedInvs) {
	return new RespectsModifiesPO(initConfig, contract, assumedInvs);
    }

    public ProofOblInput createEnsuresPostPO(InitConfig initConfig,
	    OperationContract contract, ImmutableSet<ClassInvariant> assumedInvs) {
	return new EnsuresPostPO(initConfig, contract, assumedInvs);
    }

    public ProofOblInput createPreservesInvPO(InitConfig initConfig,
	    ProgramMethod pm, ImmutableSet<ClassInvariant> assumedInvs,
	    ImmutableSet<ClassInvariant> ensuredInvs) {
	return new PreservesInvPO(initConfig, pm, assumedInvs, ensuredInvs);
    }

    public ProofOblInput createPreservesOwnInvPO(InitConfig initConfig,
	    ProgramMethod pm) {
	return new PreservesOwnInvPO(initConfig, pm);
    }

    public ProofOblInput createBehaviouralSubtypingInvPO(InitConfig initConfig,
	    KeYJavaType kjt, KeYJavaType superKJT) {
	return new BehaviouralSubtypingInvPO(initConfig, kjt, superKJT);
    }

    public ImmutableList<ProofOblInput> getRequiredCorrectnessProofsFor(
	    OperationContract atomicContract, ContractWithInvs cwi,
	    InitConfig initConfig) {

	ImmutableList<ProofOblInput> pos = ImmutableSLList
	        .<ProofOblInput> nil();

	pos = pos.prepend(createRespectsModifiesPO(initConfig, atomicContract,
	        cwi.assumedInvs));

	pos = pos.prepend(createPreservesInvPO(initConfig,
	        atomicContract.getProgramMethod(), cwi.assumedInvs,
	        cwi.ensuredInvs));

	pos = pos.prepend(createEnsuresPostPO(initConfig, atomicContract,
	        cwi.assumedInvs));
	return pos;
    }

    public ImmutableList<String> getRequiredCorrectnessProofObligationsForOperationContracts() {
	ImmutableList<String> requiredOperationCorrectnessPOs = ImmutableSLList
	        .<String> nil();
	requiredOperationCorrectnessPOs = requiredOperationCorrectnessPOs
	        .append(PRESERVES_INV);
	requiredOperationCorrectnessPOs = requiredOperationCorrectnessPOs
	        .append(ENSURES_POST);
	requiredOperationCorrectnessPOs = requiredOperationCorrectnessPOs
	        .append(RESPECTS_MODIFIES);
	return requiredOperationCorrectnessPOs;
    }

    public ProofOblInput createOperationContractPOByName(String poName,
	    ContractWithInvs cwi, InitConfig initConfig) {
	if (PRESERVES_INV.equals(poName)) {
	    return createPreservesInvPO(initConfig, cwi.contract()
		    .getProgramMethod(), cwi.assumedInvs(), cwi.ensuredInvs());
	} else if (PRESERVES_OWN_INV.equals(poName)) {
	    return createPreservesOwnInvPO(initConfig, cwi.contract()
		    .getProgramMethod());
	} else if (ENSURES_POST.equals(poName)) {
	    return createEnsuresPostPO(initConfig, cwi.contract(),
		    cwi.assumedInvs());
	} else if (RESPECTS_MODIFIES.equals(poName)) {
	    return createRespectsModifiesPO(initConfig, cwi.contract(),
		    cwi.assumedInvs());
	} else if (STRONG_OPERATION_CONTRACT.equals(poName)) {
	    return createStrongOperationContractPO(initConfig, cwi.contract(),
		    cwi.assumedInvs(), cwi.ensuredInvs());
	} else if (SPECIFICATION_EXTRACTION.equals(poName)) {
	    return createSpecExtPO(initConfig, cwi.contract(),
		    cwi.assumedInvs(), cwi.contract().getProgramMethod());
	}
	// unknown or not supported yet
	return null;
    }

}
