/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * This class is only used to generate a proof obligation for a block (see
 * {@link FunctionalBlockContractPO}.
 *
 * If a block is encountered during a proof, {@link BlockContract} is used instead.
 *
 * @author lanzinger
 */
public class FunctionalBlockContract extends FunctionalAuxiliaryContract<BlockContract> {

    /**
     *
     * @param contract a block contract.
     */
    FunctionalBlockContract(BlockContract contract) {
        super(contract);
    }

    /**
     *
     * @param contract a block contract.
     * @param id an ID.
     */
    FunctionalBlockContract(BlockContract contract, int id) {
        super(contract, id);
    }

    @Override
    public FunctionalBlockContract map(UnaryOperator<Term> op, Services services) {
        return new FunctionalBlockContract(getAuxiliaryContract().map(op, services), id());
    }

    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
        return new FunctionalBlockContractPO(initConfig, this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract) {
        assert contract instanceof FunctionalBlockContract;
        return new FunctionalBlockContractPO(initConfig, (FunctionalBlockContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig, Contract contract,
            boolean supportSymbolicExecutionAPI) {
        return createProofObl(initConfig, contract);
    }

    @Override
    public Contract setID(int newId) {
        return new FunctionalBlockContract(getAuxiliaryContract(), newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new FunctionalBlockContract(getAuxiliaryContract().setTarget(newKJT, newPM), id());
    }
}
