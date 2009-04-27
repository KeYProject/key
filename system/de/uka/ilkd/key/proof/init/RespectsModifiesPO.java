// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;


/**
 * The "RespectsModifies" proof obligation. 
 */
public class RespectsModifiesPO extends EnsuresPO {
    
    private final OperationContract contract;
    
    private Term updateAnonMethodTerm = null;
    
    
    public RespectsModifiesPO(InitConfig initConfig,
	    		      OperationContract contract,
                              SetOfClassInvariant assumedInvs) {
        super(initConfig,
              "RespectsModifies (" 
                + contract.getProgramMethod() + ", " 
                + contract.getDisplayName() + ")", 
              contract.getProgramMethod(), 
              Modality.BOX, 
              assumedInvs,
              true);
        this.contract = contract;
    }
    
        
    
    private void buildUpdateAnonMethodTerm(ProgramVariable selfVar, 
                                           ListOfProgramVariable paramVars) 
    		throws ProofInputException {
        if(updateAnonMethodTerm != null) {
            return;
        }

        //create uninterpreted heap dependent predicate symbol
        
        // find name
        final Namespace functions = services.getNamespaces().functions();
        final String anonPredBaseName = "anonHeapPred";
        
        Name anonPredName = new Name(anonPredBaseName);
        int cnt = 0;
        while (functions.lookup(anonPredName) != null) {
            anonPredName = new Name(anonPredBaseName + "_" + cnt);
            cnt++;
        }
        
        final Function anonPred = new NonRigidHeapDependentFunction(anonPredName, Sort.FORMULA, new Sort[0]);        
        registerInNamespaces(anonPred);
        
        final Term anonPredTerm = TB.func(anonPred);        
        
        //add update
        updateAnonMethodTerm = translateModifies(contract, 
                                                 anonPredTerm, 
                                                 selfVar,
                                                 toPV(paramVars));
    }
        
    
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) 
                                                throws ProofInputException {
        buildUpdateAnonMethodTerm(selfVar, paramVars);
        Term preTerm = translatePre(contract, selfVar, toPV(paramVars));
        Term result = TB.and(preTerm, updateAnonMethodTerm);
        return result;
    }
    
    
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) 
    		throws ProofInputException {
        buildUpdateAnonMethodTerm(selfVar, paramVars);
        APF.createAtPreFunctionsForTerm(updateAnonMethodTerm, 
                                        atPreFunctions, 
                                        services);
        Term result = replaceOps(atPreFunctions, updateAnonMethodTerm);
        return result;
    }
    
    
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof RespectsModifiesPO)) {
            return false;
        }
        RespectsModifiesPO rmPO = (RespectsModifiesPO) po;
        return contract.equals(rmPO.contract)
               && assumedInvs.subset(rmPO.assumedInvs);
    }
    
    
    public boolean equals(Object o) {
        if(!(o instanceof RespectsModifiesPO)) {
            return false;
        }
        RespectsModifiesPO po = (RespectsModifiesPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }
    
    
    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
