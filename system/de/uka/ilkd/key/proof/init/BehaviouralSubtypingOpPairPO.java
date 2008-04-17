// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
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

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.OperationContract;


/**
* The "BehaviouralSubtypingOpPair" proof obligation. 
*/
public class BehaviouralSubtypingOpPairPO extends AbstractPO {
  
    private OperationContract subContract;
    private OperationContract superContract;

  
  
    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
  
    public BehaviouralSubtypingOpPairPO(InitConfig initConfig,
	    				OperationContract subContract, 
                                        OperationContract superContract) {
        super(initConfig,
              "BehaviouralSubtypingOpPair for " + subContract.getProgramMethod(),
              subContract.getProgramMethod().getContainerType());
        this.subContract   = subContract;
        this.superContract = superContract;
    }
    
  
  
    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------      
  
    public void readProblem(ModStrategy mod) throws ProofInputException {
        poTerms = new Term[2];
        poNames = new String[2];
        
        //prepare variables and container for @pre-functions
        ProgramMethod programMethod     = subContract.getProgramMethod();
        ProgramVariable selfVar         = buildSelfVarAsProgVar();
        ListOfProgramVariable paramVars = buildParamVars(programMethod);
        ProgramVariable resultVar       = buildResultVar(programMethod);
        ProgramVariable exceptionVar    = buildExcVar();
        Map<Operator, Function/*atPre*/> atPreFunctions = 
            new LinkedHashMap<Operator, Function>();
      
        //build precondition implication
        Term superPreTerm 
        	= translatePre(superContract, selfVar, toPV(paramVars));
        Term subPreTerm 
        	= translatePre(subContract, selfVar, toPV(paramVars));
        poTerms[0] = TB.imp(superPreTerm, subPreTerm);
        poNames[0] = "Preconditions";
        
        //build inner postcondition implication
        Term subPostTerm = translatePost(subContract, 
                                         selfVar, 
                                         toPV(paramVars), 
                                         resultVar, 
                                         exceptionVar,
                                         atPreFunctions);
        Term superPostTerm = translatePost(superContract, 
                                           selfVar, 
                                           toPV(paramVars), 
                                           resultVar,
                                           exceptionVar,
                                           atPreFunctions);
        Term postImpTerm = TB.imp(subPostTerm, superPostTerm);
        
        //build updates
        Term postUpdateTerm = translateModifies(subContract, 
                                                postImpTerm, 
                                                selfVar,
                                                toPV(paramVars));
        
        //build definitions for @pre-functions
        Update atPreDefinitions 
            = APF.createAtPreDefinitions(atPreFunctions, services);
        
        //build postcondition implication
        poTerms[1] = TB.imp(subPreTerm, uf.apply(atPreDefinitions, 
                                                 postUpdateTerm));
        poNames[1] = "Postconditions";

        //register everything in namespaces
        registerInNamespaces(selfVar);
        registerInNamespaces(paramVars);
        registerInNamespaces(resultVar);
        registerInNamespaces(exceptionVar);
        registerInNamespaces(atPreFunctions);
    }
    

    //-------------------------------------------------------------------------
    
    protected Term getTerm1() {
        return poTerms[0];
    }
    
    
    protected Term getTerm2() {
        return poTerms[1];
    }
}
