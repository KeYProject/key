package de.uka.ilkd.key.proof.init;

import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.SetOfClassInvariant;

public class RespectsWorkingSpacePO extends EnsuresPO {

    private final OperationContract contract;
    
    public RespectsWorkingSpacePO(InitConfig initConfig, 
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
    
    @Override
    protected Term getPostTerm(ProgramVariable selfVar,
            ListOfProgramVariable paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function> atPreFunctions)
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
    protected Term getPreTerm(ProgramVariable selfVar,
            ListOfProgramVariable paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<Operator, Function> atPreFunctions)
            throws ProofInputException {
        Term result = translatePre(contract, selfVar, toPV(paramVars));
        return result;
    }
    
    protected Term buildGeneralMemoryAssumption(ProgramVariable selfVar,
            ListOfProgramVariable paramVars) 
        throws ProofInputException {
        Term result = TB.tt();
        Term workingSpace = contract.getWorkingSpace(selfVar, toPV(paramVars), services);
        if(contract.getWorkingSpace(selfVar, toPV(paramVars), services)!=null){
            ProgramVariable initialMemoryArea = services.getJavaInfo().getDefaultMemoryArea();
            Term t_mem = TB.var(initialMemoryArea);
            final ProgramVariable size = services.getJavaInfo().getAttribute(
                    "size", "javax.realtime.MemoryArea");
            final ProgramVariable consumed = services.getJavaInfo().getAttribute(
                    "consumed", "javax.realtime.MemoryArea");
            Function add = (Function) services.getNamespaces().functions().lookup(new Name("add"));
            Function leq = (Function) services.getNamespaces().functions().lookup(new Name("leq")); 
            result = TB.and(result, TB.func(leq, TB.func(add, TB.dot(t_mem,consumed), 
                    workingSpace), TB.dot(t_mem, size)));
        }
        return result;
    }

}
