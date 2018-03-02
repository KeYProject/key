package de.uka.ilkd.key.proof.init;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalLoopContract;

public class FunctionalLoopContractPO extends AbstractPO implements ContractPO {

    public static Map<Boolean,String> TRANSACTION_TAGS = new LinkedHashMap<Boolean,String>();

    private TermBuilder tb;
    private FunctionalLoopContract contract;
    private InitConfig proofConfig;

    static {
      TRANSACTION_TAGS.put(false, "transaction_inactive");
      TRANSACTION_TAGS.put(true, "transaction_active");
    }

    public FunctionalLoopContractPO(InitConfig initConfig,
            FunctionalLoopContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
    }
    
    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalBlockContractPO)) {
            return false;
        }
        
        FunctionalLoopContractPO other = (FunctionalLoopContractPO) po;
        return contract.equals(other.contract);
    }
    
    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof FunctionalBlockContractPO)) {
            return false;
        }
        
        FunctionalLoopContractPO other = (FunctionalLoopContractPO) obj;
        return contract.equals(other.contract)
                && environmentConfig.equals(other.environmentConfig);
    }

    @Override
    public void readProblem() throws ProofInputException {
        //TODO
    }

    public StatementBlock getBlock() {
        return contract.getBlock();
    }

    public KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }

    public IProgramMethod getProgramMethod() {
        return contract.getMethod();
    }

    protected Services postInit() {
       proofConfig = environmentConfig.deepCopy();
       final Services proofServices = proofConfig.getServices();
       tb = proofServices.getTermBuilder();
       return proofServices;
    }

    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return proofConfig;
    }

    @Override
    public Contract getContract() {
        return contract;
    }

    @Override
    public Term getMbyAtPre() {
        throw new UnsupportedOperationException();
    }
}
