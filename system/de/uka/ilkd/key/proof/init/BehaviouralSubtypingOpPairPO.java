//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                    Universitaet Koblenz-Landau, Germany
//                    Chalmers University of Technology, Sweden
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
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SLTranslationError;


/**
* The "BehaviouralSubtypingOpPair" proof obligation. 
*/
public class BehaviouralSubtypingOpPairPO extends AbstractPO {
  
    private OperationContract subContract;
    private OperationContract superContract;

  
  
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
  
    public BehaviouralSubtypingOpPairPO(OperationContract subContract, 
                                        OperationContract superContract) {
        super("BehaviouralSubtypingOpPair for " + subContract.getModelMethod(),
              subContract.getModelMethod().getContainingClass());
        this.subContract   = subContract;
        this.superContract = superContract;
    }
    
  
  
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------      
  
    public void readProblem(ModStrategy mod) throws ProofInputException {
        //make sure initConfig has been set
        if(initConfig == null) {
            throw new IllegalStateException("InitConfig not set.");
        }
        
        poTerms = new Term[2];
        poNames = new String[2];
        
        //prepare variables and container for @pre-functions
        ModelMethod modelMethod         = subContract.getModelMethod();
        ProgramVariable selfVar         = buildSelfVarAsProgVar();
        ListOfProgramVariable paramVars = buildParamVars(modelMethod);
        ProgramVariable resultVar       = buildResultVar(modelMethod);
        ProgramVariable exceptionVar    = buildExcVar();
        Map atPreFunctions              = new HashMap();
      
        try {
            //build precondition implication
            Term superPreTerm 
            = translatePre(superContract, selfVar, toPV(paramVars));
            Term subPreTerm 
            = translatePre(subContract, selfVar, toPV(paramVars));
            poTerms[0] = tb.imp(superPreTerm, subPreTerm);
            poNames[0] = "Preconditions";

            //build inner postcondition implication
            Term subPostTerm = translatePost(subContract, 
                    selfVar, 
                    toPV(paramVars), 
                    resultVar, 
                    exceptionVar);
            Term superPostTerm = translatePost(superContract, 
                    selfVar, 
                    toPV(paramVars), 
                    resultVar,
                    exceptionVar);
            Term postImpTerm = tb.imp(subPostTerm, superPostTerm);

            //build updates
            Term postUpdateTerm = translateModifies(subContract, 
                    postImpTerm, 
                    selfVar,
                    toPV(paramVars));

            //build definitions for @pre-functions
            Term atPreDefinitionsTerm = buildAtPreDefinitions(atPreFunctions);

            //put together @pre-definitions and sub precondition
            Term defAndSubPreTerm = tb.and(atPreDefinitionsTerm, subPreTerm);

            //build postcondition implication
            poTerms[1] = tb.imp(defAndSubPreTerm, postUpdateTerm);
            poNames[1] = "Postconditions";
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
    
    

    //-------------------------------------------------------------------------
    
    protected Term getTerm1() {
        return poTerms[0];
    }
    
    
    protected Term getTerm2() {
        return poTerms[1];
    }
}
