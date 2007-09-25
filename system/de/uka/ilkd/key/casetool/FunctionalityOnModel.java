// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool;

import java.io.File;
import java.util.*;

import de.uka.ilkd.key.casetool.together.TogetherEnvInput;
import de.uka.ilkd.key.casetool.together.TogetherModelClass;
import de.uka.ilkd.key.gui.ClassInvariantSelectionDialog;
import de.uka.ilkd.key.gui.ClassSelectionDialog;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.SuperclassSelectionDialog;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.Debug;

public class FunctionalityOnModel {
    
    private static final InvariantSelectionStrategy invStrategy 
        = InvariantSelectionStrategy.PRESELECT_CLASS; 
        
    private FunctionalityOnModel() {}

    private static String startProver(ModelClass modelClass, 
	    			      ProofOblInput po) {
	ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
	EnvInput envInput = new TogetherEnvInput((TogetherModelClass)modelClass);
	try {
	    pi.startProver(envInput, po);
	} catch(ProofInputException e) {
	    return e.toString();
	}
	return "";
    }


     /**
      * Returns the method overridden by subMethod in the passed supertype, 
      * or null if no such method exists.
      */
     private static ModelMethod getOverriddenMethod(ModelMethod subMethod, 
                                                    ModelClass supertype) {
         Vector v = supertype.getOps();
         Iterator it = v.iterator();
         String name       = subMethod.getName();
         int numParameters = subMethod.getNumParameters();
         ModelMethod overriddenMethod = null;
         while(it.hasNext()) {
             ModelMethod superMethod = (ModelMethod)(it.next());
             if(name.equals(superMethod.getName())
                && numParameters == superMethod.getNumParameters()) {
                 boolean parametersEqual = true;
                 
                 for(int i = 0; i < numParameters; i++) {
                     if(!subMethod.getParameterTypeAt(i)
                                  .equals(superMethod.getParameterTypeAt(i))) {
                         parametersEqual = false;
                         break;
                     }
                 }
                 
                 if(parametersEqual) {
                     overriddenMethod = superMethod;
                     break;
                 }
             }
         }
         
         return overriddenMethod;
     }

     
     protected static LogicVariable buildSelfVarAsLogicVar(ModelClass modelClass, JavaInfo javaInfo) {
         String className = modelClass.getFullClassName();
         KeYJavaType classType = javaInfo.getTypeByClassName(className);

         ProgramElementName classPEN = new ProgramElementName("self");
         LogicVariable result = new LogicVariable(classPEN, classType.getSort());

         return result;
     }


     protected static ListOfParsableVariable buildParamVars(ModelMethod modelMethod, JavaInfo javaInfo) {
         int numPars = modelMethod.getNumParameters();
         ListOfParsableVariable result = SLListOfParsableVariable.EMPTY_LIST;

         for(int i = 0; i < numPars; i++) {
             KeYJavaType parType
                     = javaInfo.getTypeByClassName(modelMethod.getParameterTypeAt(i));
             assert parType != null;
             ProgramElementName parPEN
                     = new ProgramElementName(modelMethod.getParameterNameAt(i));
             result = result.append(new LocationVariable(parPEN, parType));
         }

         return result;
     }


     protected static ProgramVariable buildResultVar(ModelMethod modelMethod, JavaInfo javaInfo) {
         ProgramVariable result = null;

         if(!modelMethod.isVoid()) {
             KeYJavaType resultType
                     = javaInfo.getTypeByClassName(modelMethod.getResultType());
             assert resultType != null;
             ProgramElementName resultPEN = new ProgramElementName("result");
             result = new LocationVariable(resultPEN, resultType);
         }

         return result;
     }


     protected static ProgramVariable buildExcVar(JavaInfo javaInfo) {
         KeYJavaType excType 
         	= javaInfo.getTypeByClassName("java.lang.Throwable");
         ProgramElementName excPEN = new ProgramElementName("exc");
         ProgramVariable result = new LocationVariable(excPEN, excType);

         return result;
     }


     /**
      * parse the invariant of a class if available.
      * @param aReprModelClass the class whose invariant should be parsed
      * @return error message to the user
      */
     public static String parseOneInvariant(UMLModelClass aReprModelClass) {
         String result = "";

         ListOfClassInvariant invs = aReprModelClass.getMyClassInvariants();
         if (invs.isEmpty()){
             result = "No invariant available";
         } else {

             ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
             EnvInput envInput = new TogetherEnvInput((TogetherModelClass)aReprModelClass);

             InitConfig initConf = null;

             try {
                 initConf = pi.prepare(envInput);
             } catch (ProofInputException e) {
                 e.printStackTrace();
                 Debug.fail("initialising proover failed.");
             }

             assert initConf != null;
             
             IteratorOfClassInvariant invIterator = invs.iterator();

             while(invIterator.hasNext()) {
                 try {
                     invIterator.next().getInv(initConf.getServices());
                 } catch (SLTranslationError e) {
                     result += "Error in Invariant:\n" + e.getLine() + ":" + e.getColumn() + " " + e.getMessage() + "\n\n";
                 }

                 if (initConf.getServices().getExceptionHandler().error()) {
                     Iterator errors = initConf.getServices().getExceptionHandler().getExceptions().iterator();
                     while(errors.hasNext()) {
                         Exception e = (Exception)errors.next();
                         if (e instanceof antlr.RecognitionException) {
                             result += "Error in Invariant:\n"
                                 + ((antlr.RecognitionException)e).getLine() + ":"
                                 + ((antlr.RecognitionException)e).getColumn() + " "
                                 + ((antlr.RecognitionException)e).getMessage() + "\n\n";
                         }
                     }
                 }
             }

         }

         return result.equals("") ? "No Errors were found." : result;
     }

     
     /**
      * parse the throughout property of a class if available.
      * @param aReprModelClass the class whose throughout should be parsed
      * @return error message to the user
      */
     public static String parseOneThroughout(UMLModelClass aReprModelClass) {
         String result = "";

         ListOfClassInvariant invs = aReprModelClass.getMyThroughoutClassInvariants();
         if (invs.isEmpty()){
             result = "No invariant available";
         } else {

             ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
             EnvInput envInput = new TogetherEnvInput((TogetherModelClass)aReprModelClass);

             InitConfig initConf = null;

             try {
                 initConf = pi.prepare(envInput);
             } catch (ProofInputException e) {
                 e.printStackTrace();
                 Debug.fail("initialising proover failed.");
             }

             assert initConf != null;
             
             IteratorOfClassInvariant invIterator = invs.iterator();

             while(invIterator.hasNext()) {
                 try {
                     invIterator.next().getInv(initConf.getServices());
                 } catch (SLTranslationError e) {
                     result += "Error in Invariant:\n" + e.getLine() + ":" + e.getColumn() + " " + e.getMessage() + "\n\n";
                 }

                 if (initConf.getServices().getExceptionHandler().error()) {
                     Iterator errors = initConf.getServices().getExceptionHandler().getExceptions().iterator();
                     while(errors.hasNext()) {
                         Exception e = (Exception)errors.next();
                         if (e instanceof antlr.RecognitionException) {
                             result += "Error in Invariant:\n"
                                 + ((antlr.RecognitionException)e).getLine() + ":"
                                 + ((antlr.RecognitionException)e).getColumn() + " "
                                 + ((antlr.RecognitionException)e).getMessage() + "\n\n";
                         }
                     }
                 }
             }

         }

         return result.equals("") ? "No Errors were found." : result;
     }


     /**
      * Starts the prover with an "EnsuresPost" proof obligation.
      * @param modelMethod the ModelMethod to reason about; the proof obligation 
      *                    will be about its *first* OperationContract
      * @return error message to the user
      */
     public static String parseMethodSpec(ModelMethod modelMethod) {
         //get the relevant contract
         ListOfOperationContract contracts 
         = modelMethod.getMyOperationContracts();
         if(contracts.isEmpty()) {
             return "No contracts are available for the selected method.";
         }
         OperationContract contract = contracts.head();

         String result = "";

         ProblemInitializer pi = new ProblemInitializer(Main.getInstance());
         EnvInput envInput = new TogetherEnvInput((TogetherModelClass)modelMethod.getContainingClass());

         InitConfig initConf = null;

         try {
             initConf = pi.prepare(envInput);
         } catch (ProofInputException e) {
             e.printStackTrace();
             Debug.fail("initialising proover failed.");
         }

         assert initConf != null;
         
         ParsableVariable selfVar = buildSelfVarAsLogicVar(modelMethod.getContainingClass(), initConf.getServices().getJavaInfo());

         ListOfParsableVariable paramVars = buildParamVars(modelMethod,initConf.getServices().getJavaInfo());

         ParsableVariable resultVar = buildResultVar(modelMethod,initConf.getServices().getJavaInfo());

         ParsableVariable excVar = buildExcVar(initConf.getServices().getJavaInfo());

         try {
             contract.getPre(selfVar, paramVars, initConf.getServices());
         } catch (SLTranslationError e) {
             result += "Error in Pre Condition:\n" + e.getLine() + ":" + e.getColumn() + " " + e.getMessage() + "\n\n";
         }

         if (initConf.getServices().getExceptionHandler().error()) {
             Iterator errors = initConf.getServices().getExceptionHandler().getExceptions().iterator();
             while(errors.hasNext()) {
                 Exception e = (Exception)errors.next();
                 if (e instanceof antlr.RecognitionException) {
                     result += "Error in Pre Condition:\n"
                         + ((antlr.RecognitionException)e).getLine() + ":"
                         + ((antlr.RecognitionException)e).getColumn() + " "
                         + ((antlr.RecognitionException)e).getMessage() + "\n\n";
                 }
             }
         }

         try {
             contract.getPost(selfVar, paramVars, resultVar, excVar, initConf.getServices());
         } catch (SLTranslationError e) {
             result += "Error in Post Condition:\n" + e.getLine() + ":" + e.getColumn() + " " + e.getMessage() + "\n";
         }

         if (initConf.getServices().getExceptionHandler().error()) {
             Iterator errors = initConf.getServices().getExceptionHandler().getExceptions().iterator();
             while(errors.hasNext()) {
                 Exception e = (Exception)errors.next();
                 if (e instanceof antlr.RecognitionException) {
                     result += "Error in Post Condition:\n"
                         + ((antlr.RecognitionException)e).getLine() + ":"
                         + ((antlr.RecognitionException)e).getColumn() + " "
                         + ((antlr.RecognitionException)e).getMessage() + "\n\n";
                 }
             }
         }

         return result.equals("") ? "No Errors were found." : result;
     }


     /**
      * Computes and displays the specification of the method.
      * Tries to compute the strongest specification (pre and postcondition)
      * of <code>aMethRepr</code>.
      * @param modelMethod the method whose specification to compute.
      * @return any error messages to pass to the user.
      * @see de.uka.ilkd.key.cspec.ComputeSpecification
      * @see de.uka.ilkd.key.proof.init.ComputeSpecificationPONew
      */
     public static String computeSpecification(ModelMethod modelMethod) {

    	 ProofOblInput po = new ComputeSpecificationPONew("ComputeSpecification",
                                             modelMethod);
         
         return startProver(modelMethod.getContainingClass(), po);
     }
     

     public static String transformXMIFile(ReprModel aReprModel){
         return "";
      }


     public static String proveDLFormula(ModelClass modelClass,
                                         File file) {

        CasetoolDLPO dlPOFromCasetool =  new CasetoolDLPO(modelClass, file);
        return startProver(modelClass, dlPOFromCasetool);
     }


     /** 
      * Used for OCL Simplification.
      * @param modelClass the ModelClass whose invariant needs to be simplified.
      */
     public static String simplifyInvariant(ModelClass modelClass) {
        ProofOblInput po = new OCLInvSimplPO(modelClass);
        return startProver(modelClass, po);
     }

     
    
    //-------------------------------------------------------------------------
    //New proof obligations
    //-------------------------------------------------------------------------
     
    /**
     * Asks the user to choose a supertype and then starts the prover with a 
     * corresponding "BehaviouralSubtypingInv" proof obligation.
     * @param subtype the UMLModelClass with subtype for which behavioural 
     * subtyping with respect to the invariant has to be shown
     * @return error message to the user
     */
    public static String proveBehaviouralSubtypingInv(UMLModelClass subtype) {
        //let the user select a supertype
        SuperclassSelectionDialog dlg = new SuperclassSelectionDialog(subtype);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ModelClass supertype = dlg.getSuperclass();
        if(supertype == null) {
            return "No supertype has been selected.";
        }
        if(supertype.getMyClassInvariants().isEmpty()) {
            return "Supertype does not have any invariants.";
        }
        
        //create and start the PO
        final ProofOblInput po = new BehaviouralSubtypingInvPO(subtype, 
                supertype);
        return startProver(subtype, po);
    }
    
    
    /**
     * Starts the prover with a "BehaviouralSubtypingOpPair" proof obligation.
     * @param subMethod the ModelMethod representing the overwriting method to reason about; the proof 
     *                  obligation will be about its *first* operation contract
     * @return error message to the user
     */
    public static String proveBehaviouralSubtypingOpPair(
                                                    ModelMethod subMethod){
        //get the relevant contract of the subtype method
        ListOfOperationContract subContracts 
                = subMethod.getMyOperationContracts();
        if(subContracts.isEmpty()) {
            return "No contracts are available for the selected method.";
        }
        OperationContract subContract = subContracts.head();
        
        //let the user select a supertype
        //(eventually, the user should be allowed to choose a specific contract
        //here instead of just a class)
        SuperclassSelectionDialog dlg 
                = new SuperclassSelectionDialog(subMethod.getContainingClass());
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ModelClass supertype = dlg.getSuperclass();
        if(supertype == null) {
            return "No supertype has been selected";
        }
        
        //determine the method in the chosen supertype which is overriden 
        //by the subtype method
        ModelMethod overriddenMethod = getOverriddenMethod(subMethod, 
                                                           supertype);
        if(overriddenMethod == null) {
            return "No overridden method \"" + subMethod.getName() 
                   + "\" could be found in the selected supertype.";
        }
        
        //get the relevant contract of the overridden method
        ListOfOperationContract overriddenContracts = 
                overriddenMethod.getMyOperationContracts();
        if(overriddenContracts.isEmpty()) {
            return "No contracts are available for the overridden method.";
        }
        OperationContract overriddenContract = overriddenContracts.head();
        
        //create and start the PO
        ProofOblInput po = new BehaviouralSubtypingOpPairPO(subContract,
                                                            overriddenContract);
        return startProver(supertype, po);
    }
    
    
    
    /**
     * Starts the prover with a "BehaviouralSubtypingOp" proof obligation.
     * @param subtype the UMLModelClass with the subtype for whose method
     * behavioural subtyping has to be proven
     * @return error message to the user
     */
    public static String proveBehaviouralSubtypingOp(UMLModelClass subtype){
        //let the user select a supertype
        SuperclassSelectionDialog dlg = new SuperclassSelectionDialog(subtype);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ModelClass supertype = dlg.getSuperclass();
        if(supertype == null) {
            return "No supertype has been selected";
        }
        
        //get all pairs of overriding and overridden operation contracts
        //(if there are multiple contracts for one method in either 
        //the sub- or the supertype, this currently just pairs them in the order 
        //in which they appear; eventually, the user should be asked instead)
        Map contractPairs = new HashMap();
        Vector subOps = subtype.getOps();
        Iterator it = subOps.iterator();
        while(it.hasNext()) {
            ModelMethod subMethod = (ModelMethod)(it.next());
            
            ModelMethod superMethod = getOverriddenMethod(subMethod, supertype);
            if(superMethod != null) {
                ListOfOperationContract subContracts 
                        = subMethod.getMyOperationContracts();
                ListOfOperationContract superContracts
                        = superMethod.getMyOperationContracts();
                IteratorOfOperationContract subIt = subContracts.iterator();
                IteratorOfOperationContract superIt = superContracts.iterator();
                while(subIt.hasNext() && superIt.hasNext()) {
                    contractPairs.put(subIt.next(), superIt.next());                 
                }
            }
        }
        if(contractPairs.isEmpty()) {
            return "No overridden contracts could be found "
                   + "in the selected supertype.";
        }
        
        //create and start the PO
        ProofOblInput po = new BehaviouralSubtypingOpPO(subtype, 
                                                        supertype, 
                                                        contractPairs);
        return startProver(subtype, po);
    }
    
    
    
    /**
     * Starts the prover with a "StrongOperationContract" proof obligation.
     * @param modelMethod the ModelMethod to reason about; the proof 
     *                    obligation will be about its *first* operation 
     *                    contract
     * @return error message to the user
     */
    public static String proveStrongOperationContract(ModelMethod modelMethod) {
        //get the relevant contract
        ListOfOperationContract contracts 
                = modelMethod.getMyOperationContracts();
        if(contracts.isEmpty()) {
            return "No contracts are available for the selected method.";
        }
        OperationContract contract = contracts.head();
        
        //let the user select the set of assumed invariants
        ModelClass containingClass = modelMethod.getContainingClass();
        Set modelClasses = containingClass.getAllClasses();
        
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                                    "Please select the assumed invariants",
                                    modelClasses, 
                                    false, 
                                    containingClass);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ListOfClassInvariant assumedInvs = dlg.getClassInvariants();
        if(assumedInvs.isEmpty()) {
            return "No assumed invariants have been selected.";
        }

        //let the user select the set of ensured invariants
        dlg = new ClassInvariantSelectionDialog("Select ensured invariants",
                                                modelClasses,
                                                false,
                                                containingClass);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ListOfClassInvariant ensuredInvs = dlg.getClassInvariants();
        if(ensuredInvs.isEmpty()) {
            return "No ensured invariants have been selected.";
        }
   
        //create and start the PO
        ProofOblInput po = new StrongOperationContractPO(contract,
                                                         assumedInvs,
                                                         ensuredInvs);
        return startProver(containingClass, po);
    }
    
    
    
    /**
     * Asks the user to choose a set of invariants and then starts the prover 
     * with a corresponding "PreservesInv" proof obligation.
     * @param modelMethod  the ModelMethod to reason about
     * @return error message to the user
     */
    public static String provePreservesInv(ModelMethod modelMethod) {
        ModelClass containingClass = modelMethod.getContainingClass();
        Set modelClasses = modelMethod.getContainingClass().getAllClasses();
        
        //let the user select the set of ensured invariants
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                                    "Please select the ensured invariants",
                                    modelClasses, 
                                    false, 
                                    containingClass);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ListOfClassInvariant ensuredInvs = dlg.getClassInvariants();
        if(ensuredInvs.isEmpty()) {
            return "No ensured invariants have been selected.";
        }
   
        //create and start the PO
        ProofOblInput po = new PreservesInvPO(modelMethod,
                                              invStrategy,
                                              ensuredInvs);
        return startProver(containingClass, po);
    }
    
    
    /**
     * Starts the prover with a "PreservesOwnInv" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     * @return error message to the user
     */
    public static String provePreservesOwnInv(ModelMethod modelMethod) {
	if(modelMethod.getContainingClass()
		      .getMyClassInvariants().isEmpty()) {
	    return "No own invariants are available.";
	}
	
        ProofOblInput po = new PreservesOwnInvPO(modelMethod, invStrategy);
        return startProver(modelMethod.getContainingClass(), po);
    }
    
    
    public static String provePreservesThroughout(ModelMethod modelMethod) {
        ModelClass containingClass = modelMethod.getContainingClass();
        Set modelClasses = modelMethod.getContainingClass().getAllClasses();
        
        //let the user select the set of throughout invariants
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                             "Please select the desired throughout invariants",
                             modelClasses,
                             true,
                             containingClass);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ListOfClassInvariant invariants = dlg.getClassInvariants();
        if(invariants.isEmpty()) {
            return "No throughout invariants have been selected.";
        }
   
        //create and start the PO
        ProofOblInput po = new PreservesThroughoutPO(modelMethod,
                                                     invariants,
                                                     invStrategy);
        return startProver(containingClass, po);
    }
    
    
    /**
     * Starts the prover with an "EnsuresPost" proof obligation.
     * @param modelMethod the ModelMethod to reason about; the proof obligation 
     *                    will be about its *first* OperationContract
     * @param modality the desired modality
     * @return error message to the user
     */
    public static String proveEnsuresPost(ModelMethod modelMethod,
                                          Modality modality) {
        //get the relevant contract
        ListOfOperationContract contracts 
		= modelMethod.getMyOperationContracts();
        if(contracts.isEmpty()) {
            return "No contracts are available for the selected method.";
        }
        OperationContract contract = contracts.head();

        //create and start the PO
        ProofOblInput po = new EnsuresPostPO(contract, 
                                             modality,  
                                             invStrategy);
        return startProver(modelMethod.getContainingClass(), po);
    }
    
    
    /**
     * Starts the prover with a "RespectsModifies" proof obligation.
     * @param modelMethod the ModelMethod to reason about; the proof obligation 
     *                    will be about its *first* OperationContract
     * @return error message to the user
     */
    public static String proveRespectsModifies(ModelMethod modelMethod) {
        //get the relevant contract
        ListOfOperationContract contracts 
                = modelMethod.getMyOperationContracts();
        if(contracts.isEmpty()) {
            return "No contracts are available for the selected method.";
        }
        OperationContract contract = contracts.head();
        
        //create and start the PO
        ProofOblInput po = new RespectsModifiesPO(contract, invStrategy);
        return startProver(modelMethod.getContainingClass(), po);
    }
    
    
    /**
     * Starts the prover with an "IsGuard" proof obligation.
     * @param modelMethod the ModelMethod to reason about
     * @return error message to the user
     */
    public static String provePreservesGuard(ModelMethod modelMethod) {
        ModelClass containingClass = modelMethod.getContainingClass();
        Set modelClasses = containingClass.getAllClasses();
        
        //let the user select the guarded invariants
        ClassInvariantSelectionDialog dlg = new ClassInvariantSelectionDialog(
                                        "Please select the guarded invariants",
                                        modelClasses, 
                                        false, 
                                        containingClass);
        if(!dlg.wasSuccessful()) {
            return "";
        }
        ListOfClassInvariant guardedInvs = dlg.getClassInvariants();
        if(guardedInvs.isEmpty()) {
            return "No guarded invariants have been selected.";
        }
        
        //let the user select the guard classes
        ListOfModelClass allClasses = SLListOfModelClass.EMPTY_LIST; 
        Iterator it = modelClasses.iterator();
        while(it.hasNext()) {
            allClasses = allClasses.prepend((UMLModelClass) it.next());
        }
        ClassSelectionDialog dlg2
                = new ClassSelectionDialog("Please select the guard",
                                           "Available classes",
                                           allClasses,
                                           containingClass,
                                           true);
        if(!dlg2.wasSuccessful()) {
            return "";
        }
        ListOfModelClass guard = dlg2.getSelection();
        if(guard.isEmpty()) {
            return "No guard classes have been selected.";
        }

        //create the PO
        ProofOblInput po = new PreservesGuardPO(modelMethod, 
                                         guardedInvs,
                                         guard,
                                         invStrategy);
        return startProver(containingClass, po);
    }
}
