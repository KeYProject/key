// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.speclang.ListOfClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SLTranslationError;


/**
 * The "StrongOperationContract" proof obligation.
 */
public class StrongOperationContractPO extends AbstractPO {
    
    private final OperationContract contract;
    private final ListOfClassInvariant assumedInvs;
    private final ListOfClassInvariant ensuredInvs;

    
    
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
    
    public StrongOperationContractPO(OperationContract contract, 
                                     ListOfClassInvariant assumedInvs,
                                     ListOfClassInvariant ensuredInvs) {
        super("StrongOperationContract of " + contract.getModelMethod(),
              contract.getModelMethod().getContainingClass());
        this.contract    = contract;
        this.assumedInvs = assumedInvs;
        this.ensuredInvs = ensuredInvs;
    }
    
    
    
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------     
    
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //make sure initConfig has been set
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
 
        //prepare variables and container for @pre-functions
        ModelMethod modelMethod         = contract.getModelMethod();
        ProgramVariable selfVar         = buildSelfVarAsProgVar();
        ListOfProgramVariable paramVars = buildParamVars(modelMethod);
        ProgramVariable resultVar       = buildResultVar(modelMethod);
        ProgramVariable exceptionVar    = buildExcVar();
        Map atPreFunctions              = new HashMap();
        
        try {
        	//translate precondition
	        Term preTerm = translatePre(contract, selfVar, toPV(paramVars));
	        
	        //translate and conjoin assumed invariants
	        Term assumedInvsTerm = translateInvs(assumedInvs);
	        
	        //translate postcondition
	        Term postTerm = translatePost(contract, 
	                                      selfVar, 
	                                      toPV(paramVars), 
	                                      resultVar, 
	                                      exceptionVar);
	        
	        //translate and conjoin ensured invariants
	        Term ensuredInvsTerm = translateInvs(ensuredInvs);
	        
	        //build post implication with updates
	        Term postImpTerm = tb.imp(postTerm, ensuredInvsTerm);
	        Term postUpdateTerm = translateModifies(contract, 
	                                                postImpTerm,
	                                                selfVar, 
	                                                toPV(paramVars));
	        
	        //build definitions for @pre-functions
	        Term atPreDefinitionsTerm = buildAtPreDefinitions(atPreFunctions);
	   
	        //put together @pre-definitions, precondition, and assumed invariants
	        Term defAndPreAndAssumedInvsTerm = tb.and(atPreDefinitionsTerm, 
	                                                  tb.and(preTerm, 
	                                                         assumedInvsTerm));
	        
	        //build top level implication
	        Term poTerm = tb.imp(defAndPreAndAssumedInvsTerm, postUpdateTerm);
	        poTerms = new Term[]{poTerm};
        } catch (SLTranslationError e) {
        	throw new ProofInputException(e);
        }
        
        //register everything in namespaces
        registerInNamespaces(selfVar);
        registerInNamespaces(paramVars);
        registerInNamespaces(resultVar);
        registerInNamespaces(exceptionVar);
        registerInNamespaces(atPreFunctions);
    }


    public Contractable[] getObjectOfContract() {
        return new Contractable[0];
    }

    
    public boolean initContract(Contract ct) {
        return false;
    }
}
