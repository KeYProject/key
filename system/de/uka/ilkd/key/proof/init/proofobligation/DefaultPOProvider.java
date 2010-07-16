package de.uka.ilkd.key.proof.init.proofobligation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.RTSJProfile;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

public class DefaultPOProvider {

    public ImmutableList<String> getPOsFor(SpecificationRepository specRepos, ProgramMethod pm) {
        ImmutableList<String> pos = ImmutableSLList.<String> nil();
    
        /*
         * //BehaviouralSubtypingOpPair
         * if(specRepos.getOperationContracts(pm).size() > 0 &&
         * javaInfo.getDirectSuperTypes(pm.getContainerType()).size() > 0) { pos
         * = pos.append("BehaviouralSubtypingOpPair"); }
         */
    
        // StrongOperationContract
        if (specRepos.getOperationContracts(pm).size() > 0) {
            pos = pos.append("StrongOperationContract");
        }
    
        // PreservesInv
        pos = pos.append("PreservesInv");
    
        // PreservesOwnInv
        if (specRepos.getClassInvariants(pm.getContainerType()).size() > 0) {
            pos = pos.append("PreservesOwnInv");
        }
    
        // EnsuresPost
        if (specRepos.getOperationContracts(pm).size() > 0) {
            pos = pos.append("EnsuresPost");
        }
    
        // RespectsWorkingSpace
        if (specRepos.getOperationContracts(pm).size() > 0
                && (ProofSettings.DEFAULT_SETTINGS.getProfile() instanceof RTSJProfile && ((RTSJProfile) ProofSettings.DEFAULT_SETTINGS
                        .getProfile()).memoryConsumption())) {
            pos = pos.append("RespectsWorkingSpace");
        }
    
        // RespectsModifies
        if (specRepos.getOperationContracts(pm).size() > 0) {
            pos = pos.append("RespectsModifies");
        }
    
        // implemented by mbender for jmltest
        // Specification Extraction
        if (specRepos.getOperationContracts(pm).size() > 0) {
            pos = pos.append("SpecificationExtraction");
        }
    
        // PreservesGuard
        pos = pos.append("PreservesGuard");
        return pos;
    }

    public ImmutableList<String> getPOsFor(SpecificationRepository specRepos, JavaInfo javaInfo, KeYJavaType kjt) {
        ImmutableList<String> pos = ImmutableSLList.<String>nil();
    
        //BehaviouralSubtypingInv
        if(specRepos.getClassInvariants(kjt).size() > 0
           && javaInfo.getDirectSuperTypes(kjt).size() > 0) {
            pos = pos.append("BehaviouralSubtypingInv");
        }
    
    /*        
        //BehaviouralSubtypingOp
        IList<ProgramMethod> pms = javaInfo.getAllProgramMethods(kjt);
        Iterator<ProgramMethod> it = pms.iterator();
        boolean foundContract = false;
        while(it.hasNext()) {
            ProgramMethod pm = it.next();
            if(specRepos.getOperationContracts(pm).size() > 0) {
        	foundContract = true;
        	break;
            }
        }
        if(foundContract && javaInfo.getDirectSuperTypes(kjt).size() > 0) {
            pos = pos.append("BehaviouralSubtypingOp");
        }	
    */
        return pos;
    }

    public ProofOblInput createStrongOperationContractPO(InitConfig initConfig,
	    OperationContract contract,
	    ImmutableSet<ClassInvariant> assumedInvs,
	    ImmutableSet<ClassInvariant> ensuredInvs) {
	return new StrongOperationContractPO(initConfig, contract, assumedInvs, ensuredInvs);
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

    public ProofOblInput createRespectsWorkingSpacePO(InitConfig initConfig,
            OperationContract contract, ImmutableSet<ClassInvariant> assumedInvs) {
	return new RespectsWorkingSpacePO(initConfig, contract, assumedInvs);
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

    
    
}
