/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init.loader;

import java.io.IOException;

import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
@NullMarked
public class FunctionOperationContractPOLoader implements ProofObligationLoader {
    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties) throws IOException {
        String contractName = properties.getString("contract");
        int proofNum = 0;
        String baseContractName;
        int ind = -1;
        for (String tag : FunctionalOperationContractPO.TRANSACTION_TAGS.values()) {
            ind = contractName.indexOf("." + tag);
            if (ind > 0) {
                break;
            }
            proofNum++;
        }
        if (ind == -1) {
            baseContractName = contractName;
            proofNum = 0;
        } else {
            baseContractName = contractName.substring(0, ind);
        }
        final Contract contract = initConfig.getServices().getSpecificationRepository()
                .getContractByName(baseContractName);
        if (contract == null) {
            throw new IOException("Contract not found: " + baseContractName);
        } else {
            ProofOblInput po;
            boolean addUninterpretedPredicate =
                AbstractOperationPO.isAddUninterpretedPredicate(properties);
            boolean addSymbolicExecutionLabel =
                AbstractOperationPO.isAddSymbolicExecutionLabel(properties);
            if (addUninterpretedPredicate || addSymbolicExecutionLabel) {
                if (!(contract instanceof FunctionalOperationContract)) {
                    throw new IOException(
                        "Found contract \"" + contract + "\" is no FunctionalOperationContract.");
                }
                po = new FunctionalOperationContractPO(initConfig,
                    (FunctionalOperationContract) contract, addUninterpretedPredicate,
                    addSymbolicExecutionLabel);
            } else {
                po = contract.createProofObl(initConfig);
            }
            return new IPersistablePO.LoadedPOContainer(po, proofNum);
        }
    }

    @Override
    public boolean handles(String identifier) {
        return FunctionalOperationContractPO.class.getName().equals(identifier)
                || FunctionalOperationContractPO.class.getSimpleName().equals(identifier)
                || getClass().getName().equals(identifier)
                || getClass().getSimpleName().equals(identifier);
    }
}
