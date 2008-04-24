package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;

public class RespectsWorkingSpacePO extends EnsuresPostPO {

    private final OperationContract contract;
    
    public RespectsWorkingSpacePO(InitConfig initConfig,
                         OperationContract contract, 
                         SetOfClassInvariant assumedInvs) {
        super(initConfig, 
              "RespectsWorkingSpace", 
              contract,
              assumedInvs);
        this.contract = contract;
    }
    
    @Override
    protected Term getPostTerm(ProgramVariable selfVar,
            ListOfProgramVariable paramVars, ProgramVariable resultVar,
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
            ListOfProgramVariable paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function> atPreFunctions)
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }
    
}
