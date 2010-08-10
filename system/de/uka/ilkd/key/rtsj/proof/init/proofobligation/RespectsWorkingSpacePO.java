// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rtsj.proof.init.proofobligation;

import java.util.Map;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.OperationContract;

public class RespectsWorkingSpacePO extends EnsuresPostPO {
    
    RespectsWorkingSpacePO(InitConfig initConfig,
                         OperationContract contract, 
                         ImmutableSet<ClassInvariant> assumedInvs) {
        super(initConfig, 
              "RespectsWorkingSpace", 
              contract,
              assumedInvs);
    }
    
    @Override
    protected Term getPostTerm(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function> atPreFunctions)
            throws ProofInputException {
        Term result = translateWorkingSpacePost(contract, 
                selfVar, 
                toPV(paramVars), 
                resultVar, 
                exceptionVar,
                atPreFunctions);
        return result;
    }

    @Override
    protected Term getPreTerm(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function> atPreFunctions)
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }
    
}
