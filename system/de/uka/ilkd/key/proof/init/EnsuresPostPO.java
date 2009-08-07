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

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ListOfProgramVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;


/**
 * The "EnsuresPost" proof obligation. 
 */
public final class EnsuresPostPO extends EnsuresPO {
    
    private final OperationContract contract;
    
    public EnsuresPostPO(InitConfig initConfig, 
                         String name,
                         OperationContract contract, 
                         SetOfClassInvariant assumedInvs) {
        super(initConfig, 
              name, 
              contract.getProgramMethod(), 
              contract.getModality(), 
              assumedInvs, 
              true);
        this.contract = contract;
    }


    public EnsuresPostPO(InitConfig initConfig, OperationContract contract,
            SetOfClassInvariant assumedInvs) {
        this(initConfig, 
             "EnsuresPost (" 
                 + contract.getProgramMethod() + ", " 
                 + contract.getDisplayName() + ")", 
             contract, 
             assumedInvs);
    }
    
    
    @Override
    protected Term getPreTerm(ProgramVariable selfVar, 
                              ListOfProgramVariable paramVars, 
                              ProgramVariable resultVar,
                              ProgramVariable exceptionVar,
                              Map<Operator, Function/*atPre*/> atPreFunctions) 
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }
    
    
    @Override
    protected Term getPostTerm(ProgramVariable selfVar, 
                               ListOfProgramVariable paramVars, 
                               ProgramVariable resultVar,
                               ProgramVariable exceptionVar,
                               Map<Operator, Function/*atPre*/> atPreFunctions) 
            throws ProofInputException {        
        Term result = translatePost(contract, 
                                    selfVar, 
                                    toPV(paramVars), 
                                    resultVar, 
                                    exceptionVar,
                                    atPreFunctions);
       
        return result;
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if(!(po instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO epPO = (EnsuresPostPO) po;
        return specRepos.splitContract(epPO.contract)
                        .subset(specRepos.splitContract(contract))
               && assumedInvs.subset(epPO.assumedInvs);
    }
    
    
    @Override
    public boolean equals(Object o) {
        if(!(o instanceof EnsuresPostPO)) {
            return false;
        }
        EnsuresPostPO po = (EnsuresPostPO) o;
        return super.equals(po)
               && contract.equals(po.contract);
    }
    
    
    @Override
    public int hashCode() {
        return super.hashCode() + contract.hashCode();
    }
}
