// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.together;

import java.io.File;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.casetool.ModelClass;
import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.cspec.ComputeSpecificationPO;
import de.uka.ilkd.key.gui.ClassInvariantSelectionDialog;
import de.uka.ilkd.key.gui.ClassSelectionDialog;
import de.uka.ilkd.key.gui.ContractConfigurator;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;
import de.uka.ilkd.key.speclang.SetOfOperationContract;



public class FunctionalityOnModel {
    
    private FunctionalityOnModel() {}
    

    
    //-------------------------------------------------------------------------
    //Internal methods
    //-------------------------------------------------------------------------
    
    /**
     * Tells whether the passed model class has a class invariant.
     */
    private static boolean hasAnInvariant(ModelClass modelClass) {
	return modelClass.getMyInv() != null 
	       && !modelClass.getMyInv().equals("");
    }
    

    /**
     * Tells whether the passed model class has a throughout invariant.
     */
    private static boolean hasAThroughoutInvariant(ModelClass modelClass) {
	return modelClass.getMyThroughout() != null
	       && !modelClass.getMyThroughout().equals("");
    }

    
    /**
     * Tells whether the passed model method has an operation contract.  
     */
    private static boolean hasAContract(ModelMethod modelMethod) {
	return modelMethod.getMyPreCond() != null
			&& !modelMethod.getMyPreCond().equals("")
	       || modelMethod.getMyPostCond() != null
	       		&& !modelMethod.getMyPostCond().equals("")
	       || modelMethod.getMyModifClause() != null
	       		&& !modelMethod.getMyModifClause().equals("");
    }
    

    /**
     * Returns the method overridden by subMethod in the passed supertype, 
     * or null if no such method exists.
     */
    private static ProgramMethod getOverriddenMethod(
	     				ProgramMethod subMethod, 
                                        KeYJavaType superKJT,
                                        JavaInfo javaInfo) {
	String name       = subMethod.getName();
	int numParameters = subMethod.getParameterDeclarationCount();
	 
        IteratorOfProgramMethod it 
         	= javaInfo.getAllProgramMethods(superKJT).iterator();
        while(it.hasNext()) {
            ProgramMethod superMethod = it.next();
            if(name.equals(superMethod.getName())
               && numParameters == superMethod.getParameterDeclarationCount()) {
        	boolean parametersEqual = true;
        	for(int i = 0; i < numParameters; i++) {
        	    if(!subMethod.getParameterType(i)
                                 .equals(superMethod.getParameterType(i))) {
        		parametersEqual = false;
        		break;
        	    }
        	}
                     
        	if(parametersEqual) {
        	    return superMethod;
        	}
            }
        }
         
        return null;
    }
    
    
    /**
     * Finds the KJT corresponding to a ModelClass.
     */
    private static KeYJavaType getKJT(ModelClass modelClass, 
	    			      JavaInfo javaInfo) {
	assert modelClass != null;
	KeYJavaType result 
		= javaInfo.getTypeByClassName(modelClass.getFullClassName());
	assert result != null : "KJT not found : \"" 
	    			+ modelClass.getFullClassName() + "\"";
	return result;
    }    
    
    
    /**
     * Finds the ProgramMethod corresponding to a ModelMethod.
     */
    private static ProgramMethod getProgramMethod(ModelMethod modelMethod,
	    				   	  JavaInfo javaInfo) {
	assert modelMethod != null;
	KeYJavaType containingClass = getKJT(modelMethod.getContainingClass(), 
					     javaInfo);
	
	//collect signature KJTs
	ListOfKeYJavaType signature = SLListOfKeYJavaType.EMPTY_LIST;           
        for(int i = 0; i < modelMethod.getNumParameters(); i++) {
            String parTypeName = modelMethod.getParameterTypeAt(i);
            KeYJavaType kjt = javaInfo.getTypeByClassName(parTypeName);
            assert kjt != null : "KJT not found: \"" + parTypeName + "\"";
            signature = signature.append(kjt);
        }
        
        //determine name ("<init>" for constructors)
        String operationName 
        	= modelMethod.getName().equals(containingClass.getName())
        	  ? "<init>"
        	  : modelMethod.getName();

        //ask javaInfo
        ProgramMethod result 
        	= javaInfo.getProgramMethod(containingClass,
                               		    operationName,
                                            signature,
                                            containingClass);
        assert result != null : "ProgramMethod not found: \"" 
            			+ operationName + "\""
        			+ "\nsignature: " + signature
        			+ "\ncontainer: " + containingClass;
        return result;
    }
    
    
    /**
     * Lets the user select a supertype of subKJT in a dialog window.
     */
    private static KeYJavaType askUserForSupertype(KeYJavaType subKJT, 
	    				    	   JavaInfo javaInfo) {
	//collect supertypes
	SetOfKeYJavaType superKJTs = SetAsListOfKeYJavaType.EMPTY_SET;
	IteratorOfKeYJavaType it = javaInfo.getAllSupertypes(subKJT).iterator();
	while(it.hasNext()) {
	    superKJTs = superKJTs.add(it.next());
	}
	
	//ask user
        ClassSelectionDialog dlg = new ClassSelectionDialog(
        		"Please select a supertype",
        		"Supertypes of " + subKJT.getName(),
        		superKJTs,
        		false);
        if(!dlg.wasSuccessful()) {
            return null;
        }
        
        //return selection
        SetOfKeYJavaType selectedKJTs = dlg.getSelection();
        if(selectedKJTs.size() == 0) {
            return null;
        } else {
            return selectedKJTs.iterator().next();
        }
    }
         

    /**
     * Reads a TogetherEnvInput, i.e. the Java model, standard rules, 
     * and OCL specifications.
     */
    private static InitConfig prepare(ModelClass anyModelClass) 
    		throws ProofInputException {
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	EnvInput envInput 
		= new TogetherEnvInput((TogetherModelClass) anyModelClass);
	return pi.prepare(envInput);	
    }
    

    /**
     * Same as prepare(), except:
     * (1) no specifications are translated, and
     * (2) the prover window is not shown
     *     (though probably we *should* give the user *some* feedback, because
     *      at least on the first time, when the standard rules have to be loaded,
     *      this takes rather long).
     */
    private static InitConfig prepareSilent(ModelClass anyModelClass) 
    		throws ProofInputException {
	Profile profile = Main.getInstance(false).mediator().getProfile();
 	ProblemInitializer pi = new ProblemInitializer(profile);
 	EnvInput envInput 
 		= new TogetherEnvInput((TogetherModelClass) anyModelClass, 
 				       false);
 	return pi.prepare(envInput);	
    }

    
    /**
     * Starts the prover with the given PO.
     */
    private static void startProver(InitConfig initConfig, ProofOblInput po) 
    		throws ProofInputException {
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	pi.startProver(initConfig, po);
    }
    
    
    
    //-------------------------------------------------------------------------
    //Class menu
    //-------------------------------------------------------------------------
    
    /**
     * Checks a class invariant for syntactic correctness.
     */
    public static void parseClassSpec(TogetherModelClass modelClass) 
    		throws ProofInputException {
	assert false; //TODO
    }
   
    
    /** 
     * Starts OCL Simplification.
     */
    public static void simplifyInvariant(TogetherModelClass modelClass) 
    		throws ProofInputException {
	ProofOblInput po = new OCLInvSimplPO(modelClass);
        startProver(prepare(modelClass), po);
    }
    
    
    /**
     * Starts the prover with a proof obligation specified in a .key file.
     */
    public static void proveDLFormula(TogetherModelClass modelClass, 
	     			      File file) 
     		throws ProofInputException {
	CasetoolDLPO dlPOFromCasetool =  new CasetoolDLPO(modelClass, file);
        startProver(prepare(modelClass), dlPOFromCasetool);
    }

    
    /**
     * Asks the user to choose a supertype and then starts the prover with a 
     * corresponding "BehaviouralSubtypingInv" proof obligation.
     * @param subType the UMLModelClass with subtype for which behavioural 
     * subtyping with respect to the invariant has to be shown
     */
    public static void proveBehaviouralSubtypingInv(TogetherModelClass subType) 
    		throws ProofInputException {
	//no invariant in subtype?
	if(!hasAnInvariant(subType)) {
	    throw new ProofInputException("The selected subtype does not have "
		    			  + "an invariant.");
	}
	
       	//prepare
	InitConfig initConfig = prepare(subType);
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	
        //let the user select a supertype
	KeYJavaType subKJT = getKJT(subType, javaInfo);
	KeYJavaType superKJT = askUserForSupertype(subKJT, javaInfo);
	if(superKJT == null) {
	    return;
	}
                
        //create and start the PO
        ProofOblInput po = new BehaviouralSubtypingInvPO(initConfig, 
        					         subKJT, 
        					         superKJT);
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with a "BehaviouralSubtypingOp" proof obligation.
     * @param subType the {@link TogetherModelClass} with the subtype for whose method
     * behavioural subtyping has to be proven
     */
    public static void proveBehaviouralSubtypingOp(TogetherModelClass subType) 
    		throws ProofInputException {
       	//prepare
	InitConfig initConfig = prepare(subType);
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        SpecificationRepository specRepos 
        	= initConfig.getServices().getSpecificationRepository();

        //let the user select a supertype
	KeYJavaType subKJT   = getKJT(subType, javaInfo);
	KeYJavaType superKJT = askUserForSupertype(subKJT, javaInfo);
	if(superKJT == null) {
	    return;
	}
        
        //get all pairs of overriding and overridden operation contracts
        //(only works correctly if there cannot be more than one contract per 
	// operation, as it is currently the case in Together)
        Map<OperationContract, OperationContract> contractPairs = 
            new HashMap<OperationContract, OperationContract>();
        IteratorOfProgramMethod subIt 
        	= javaInfo.getAllProgramMethods(subKJT).iterator();
        while(subIt.hasNext()) {
            ProgramMethod subPM = subIt.next();
            ProgramMethod superPM = getOverriddenMethod(subPM, 
        	    					superKJT, 
        	    					javaInfo);
            
            if(superPM != null) {
                SetOfOperationContract subContracts 
                        = specRepos.getOperationContracts(subPM, 
                        				  Modality.BOX);
                SetOfOperationContract superContracts
                        = specRepos.getOperationContracts(superPM, 
                        				  Modality.BOX);
                if(subContracts.size() > 0 && superContracts.size() > 0) {
                    contractPairs.put(subContracts.iterator().next(), 
                	    	      superContracts.iterator().next());
                }
            }
        }
        if(contractPairs.isEmpty()) {
            throw new ProofInputException("No overridden contracts could be "
        	    			  + "found in the selected supertype.");
        }
        
        //create and start the PO
        ProofOblInput po = new BehaviouralSubtypingOpPO(initConfig,
        						subKJT, 
                                                        superKJT, 
                                                        contractPairs);
        startProver(initConfig, po);
    }
    

    
    //-------------------------------------------------------------------------
    //Operation menu
    //-------------------------------------------------------------------------
    
    /**
     * Checks an operation contract for syntactic correctness.
     * @param modelMethod the ModelMethod to reason about
     */
    public static void parseMethodSpec(TogetherModelMethod modelMethod) 
    		throws ProofInputException {
 	assert false; //TODO
    }
    
    
    /**
     * Computes and displays the specification of the method.
     * Tries to compute the strongest specification (pre and postcondition)
     * of <code>aMethRepr</code>.
     * @param modelMethod the method whose specification to compute.
     */
    public static void computeSpecification(ModelMethod modelMethod) 
    		throws ProofInputException {
	//prepare
	InitConfig initConfig = prepare(modelMethod.getContainingClass());
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	
	//get program method
	ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
	
	//create and start the PO
	ProofOblInput po = new ComputeSpecificationPO(initConfig, pm);
	startProver(prepare(modelMethod.getContainingClass()), po);
    }

    
    /**
     * Starts the prover with a "BehaviouralSubtypingOpPair" proof obligation.
     * @param subMethod the overwriting method to reason about
     */
    public static void proveBehaviouralSubtypingOpPair(
	    					TogetherModelMethod subMethod) 
    		throws ProofInputException {
	//no contract for subMethod?
	if(!hasAContract(subMethod)) {
	    throw new ProofInputException("The selected operation "
		    			  + "does not have a contract.");
	}
	
        //prepare
        InitConfig initConfig = prepare(subMethod.getContainingClass());
        SpecificationRepository specRepos 
        	= initConfig.getServices().getSpecificationRepository();
        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	
	//let the user select a supertype
	KeYJavaType subKJT   = getKJT(subMethod.getContainingClass(), javaInfo);
	KeYJavaType superKJT = askUserForSupertype(subKJT, javaInfo);
	if(superKJT == null) {
	    return;
	}
        
        //determine the method in the chosen supertype which is overriden 
        //by the sub type method
	ProgramMethod subPM = getProgramMethod(subMethod, javaInfo);
	ProgramMethod superPM = getOverriddenMethod(subPM, superKJT, javaInfo);
        if(superPM == null) {
            throw new ProofInputException(
        	   "No overridden method \"" + subMethod.getName() 
                   + "\" could be found in the selected supertype.");
        }
        	
        //get contracts
        SetOfOperationContract subContracts 
        	= specRepos.getOperationContracts(subPM, Modality.BOX);
        assert subContracts.size() > 0;
        SetOfOperationContract superContracts
                = specRepos.getOperationContracts(superPM, Modality.BOX);
        if(superContracts.size() == 0) {
            throw new ProofInputException("The overridden method "
        	    			  + " does not have a contract.");
        }
        OperationContract subContract = subContracts.iterator().next();
        OperationContract superContract = superContracts.iterator().next();
        
        //create and start the PO
        ProofOblInput po = new BehaviouralSubtypingOpPairPO(initConfig,
        						    subContract,
                                                            superContract);
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with a "StrongOperationContract" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     */
    public static void proveStrongOperationContract(
	    				TogetherModelMethod modelMethod) 
		throws ProofInputException {
	TogetherModelClass containingClass 
		= (TogetherModelClass) modelMethod.getContainingClass();

	//no contract?
	if(!hasAContract(modelMethod)) {
	    throw new ProofInputException("The selected operation "
		    			  + " does not have a contract.");
	}
	
	//prepare
	InitConfig initConfig = prepare(containingClass);
	SpecificationRepository specRepos 
		= initConfig.getServices().getSpecificationRepository();
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	
        //let the user select the set of assumed invariants
	KeYJavaType kjt = getKJT(containingClass, javaInfo);
	ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                                    "Please select the assumed invariants",
                                    initConfig.getServices(), 
                                    false, 
                                    kjt);
        if(!dlg.wasSuccessful()) {
            return;
        }
        SetOfClassInvariant assumedInvs = dlg.getSelection();
        if(assumedInvs.size() == 0) {
            throw new ProofInputException("No assumed invariants "
        	    			  + "have been selected.");
        }

        //let the user select the set of ensured invariants
        dlg = new ClassInvariantSelectionDialog(
        			     "Please select the ensured invariants",
                                     initConfig.getServices(),
                                     false,
                                     kjt);
        if(!dlg.wasSuccessful()) {
            return;
        }
        SetOfClassInvariant ensuredInvs = dlg.getSelection();
        if(ensuredInvs.size() == 0) {
            throw new ProofInputException("No ensured invariants "
        	    			  + " have been selected.");
        }
        
        //get contract
        SetOfOperationContract contracts 
        	= specRepos.getOperationContracts(pm, Modality.BOX);
        assert contracts.size() > 0;
        OperationContract contract = contracts.iterator().next();
   
        //create and start the PO
        ProofOblInput po = new StrongOperationContractPO(initConfig,
        						 contract,
                                                         assumedInvs,
                                                         ensuredInvs);
        startProver(initConfig, po);
    }
    
    
    /**
     * Asks the user to choose a set of invariants and then starts the prover 
     * with a corresponding "PreservesInv" proof obligation.
     * @param modelMethod  the ModelMethod to reason about
     */
    public static void provePreservesInv(TogetherModelMethod modelMethod) 
    		throws ProofInputException {
        TogetherModelClass containingClass 
        	= (TogetherModelClass) modelMethod.getContainingClass();
        
        //prepare
        InitConfig initConfig = prepare(containingClass);
        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        
        //let the user select the set of ensured invariants
        KeYJavaType kjt = getKJT(containingClass, javaInfo);
        ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
        ContractConfigurator cc 
            = new ContractConfigurator(Main.getInstance(),
                                       initConfig.getServices(),
                                       pm,
                                       null,
                                       false,
                                       true,
                                       true);
        if(!cc.wasSuccessful()) {
            return;
        }     
        if(cc.getEnsuredInvs().size() == 0) {
            throw new ProofInputException("No ensured invariants "
        	    			  + "have been selected.");
        }
   
        //create and start the PO
        ProofOblInput po = new PreservesInvPO(initConfig, 
                                              pm, 
                                              cc.getAssumedInvs(), 
                                              cc.getEnsuredInvs());
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with a "PreservesOwnInv" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     */
    public static void provePreservesOwnInv(TogetherModelMethod modelMethod) 
    		throws ProofInputException {
        TogetherModelClass containingClass 
        	= (TogetherModelClass) modelMethod.getContainingClass();
	
	//no invariant?
	if(!hasAnInvariant(containingClass)) {
	    throw new ProofInputException("No own invariants are available.");
	}
	
	//prepare
	InitConfig initConfig = prepare(containingClass);
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	
	//create and start the PO
	ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
        ProofOblInput po = new PreservesOwnInvPO(initConfig, pm);
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with a "PreservesThroughout" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     */
    public static void provePreservesThroughout(TogetherModelMethod modelMethod) 
    		throws ProofInputException {
        TogetherModelClass containingClass 
        	= (TogetherModelClass) modelMethod.getContainingClass();
        
        //prepare
        InitConfig initConfig = prepare(containingClass);
        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        
        //let the user select the set of throughout invariants
        KeYJavaType kjt = getKJT(containingClass, javaInfo);
        ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                             "Please select the desired throughout invariants",
                             initConfig.getServices(),
                             true,
                             kjt);
        if(!dlg.wasSuccessful()) {
            return;
        }
        SetOfClassInvariant invariants = dlg.getSelection();
        if(invariants.size() == 0) {
            throw new ProofInputException("No throughout invariants "
        	    			  + "have been selected.");
        }
   
        //create and start the PO
        ProofOblInput po = new PreservesThroughoutPO(initConfig,
        					     pm,
                                                     invariants);
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with an "EnsuresPost" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     */
    public static void proveEnsuresPost(TogetherModelMethod modelMethod) 
    		throws ProofInputException {
	//no contract?
	if(!hasAContract(modelMethod)) {
	    throw new ProofInputException("The selected operation "
		    			  + "does not have a contract.");
	}
	
	//prepare
	InitConfig initConfig = prepare(modelMethod.getContainingClass());
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	
        //let the user select the contract and the assumed invariants
        ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
        ContractConfigurator cc 
            = new ContractConfigurator(Main.getInstance(),
                                       initConfig.getServices(),
                                       pm,
                                       null,
                                       true,
                                       true,
                                       false);
        if(!cc.wasSuccessful()) {
            return;
        }     

        //create and start the PO
        ProofOblInput po = new EnsuresPostPO(initConfig, 
                                             cc.getContract(), 
                                             cc.getAssumedInvs());
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with a "RespectsModifies" proof obligation.
     * @param modelMethod the ModelMethod to reason about; the proof obligation 
     *                    will be about a random one of its OperationContracts
     */
    public static void proveRespectsModifies(TogetherModelMethod modelMethod)
    		throws ProofInputException {
	//no contract?
	if(!hasAContract(modelMethod)) {
	    throw new ProofInputException("The selected operation "
		    			  + "does not have a contract.");
	}
	
	//prepare
	InitConfig initConfig = prepare(modelMethod.getContainingClass());
	JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
	SpecificationRepository specRepos 
		= initConfig.getServices().getSpecificationRepository();
	
	//let the user select the contract and the assumed invariants
        ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);
        ContractConfigurator cc 
            = new ContractConfigurator(Main.getInstance(),
                                       initConfig.getServices(),
                                       pm,
                                       null,
                                       true,
                                       true,
                                       false);
        if(!cc.wasSuccessful()) {
            return;
        } 
        
        //create and start the PO
        ProofOblInput po = new RespectsModifiesPO(initConfig, 
                                                  cc.getContract(), 
                                                  cc.getAssumedInvs());
        startProver(initConfig, po);
    }
    
    
    /**
     * Starts the prover with an "IsGuard" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     */
    public static void provePreservesGuard(TogetherModelMethod modelMethod) 
    		throws ProofInputException {
        //prepare
        InitConfig initConfig = prepare(modelMethod.getContainingClass());
        JavaInfo javaInfo = initConfig.getServices().getJavaInfo();
        
        
        //let the user select the guarded invariants
        KeYJavaType kjt = getKJT(modelMethod.getContainingClass(), javaInfo);
        ProgramMethod pm = getProgramMethod(modelMethod, javaInfo);       
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                                        "Please select the guarded invariants",
                                        initConfig.getServices(), 
                                        false, 
                                        kjt);
        if(!dlg.wasSuccessful()) {
            return;
        }
        SetOfClassInvariant guardedInvs = dlg.getSelection();
        if(guardedInvs.size() == 0) {
            throw new ProofInputException("No guarded invariants "
        	    			  + "have been selected.");
        }
        
        //let the user select the guard classes
	SetOfKeYJavaType allKJTs = SetAsListOfKeYJavaType.EMPTY_SET;
	final Iterator<KeYJavaType> it = javaInfo.getAllKeYJavaTypes().iterator();
	while(it.hasNext()) {
	    allKJTs = allKJTs.add(it.next());
	}
        ClassSelectionDialog dlg2
                = new ClassSelectionDialog("Please select the guard",
                                           "Available classes",
                                           allKJTs,
                                           kjt,
                                           true);
        if(!dlg2.wasSuccessful()) {
            return;
        }
        SetOfKeYJavaType guard = dlg2.getSelection();
        if(guard.size() == 0) {
            throw new ProofInputException("No guard classes "
        	    			  + "have been selected.");
        }

        //create and start the PO
        ProofOblInput po = new PreservesGuardPO(initConfig, 
        					pm, 
        					guardedInvs,
        					guard);
        startProver(initConfig, po);
    }
}
