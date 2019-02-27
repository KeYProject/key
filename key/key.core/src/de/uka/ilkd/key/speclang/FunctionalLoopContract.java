package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalLoopContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * This class is only used to generate a proof obligation for a block that starts with a loop (see
 * {@link FunctionalLoopContractPO}.
 *
 * If a block is encountered during a proof, {@link LoopContract} is used instead.
 *
 * @author lanzinger
 */
public class FunctionalLoopContract extends FunctionalAuxiliaryContract<LoopContract> {

    /**
     *
     * @param contract
     *            a loop contract.
     */
    FunctionalLoopContract(LoopContract contract) {
        super(contract);
    }

    /**
     *
     * @param contract
     *            a loop contract.
     * @param id
     *            an ID.
     */
    FunctionalLoopContract(LoopContract contract, int id) {
        super(contract, id);
    }

    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
        return new FunctionalLoopContractPO(initConfig, this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        assert contract instanceof FunctionalLoopContract;
        return new FunctionalLoopContractPO(initConfig, (FunctionalLoopContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean supportSymbolicExecutionAPI) {
        return createProofObl(initConfig, contract);
    }

    @Override
    public Contract setID(int newId) {
        return new FunctionalLoopContract(getAuxiliaryContract(), newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new FunctionalLoopContract(getAuxiliaryContract().setTarget(newKJT, newPM), id());
    }

    public void replaceEnhancedForVariables(Services services) {
        contract = contract.replaceEnhancedForVariables(contract.getBlock(), services);
    }
}
