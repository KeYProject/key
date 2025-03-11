/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init.loader;

import java.util.Objects;

import de.uka.ilkd.key.proof.init.DependencyContractPO;
import de.uka.ilkd.key.proof.init.FunctionalOperationContractPO;
import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;

import org.jspecify.annotations.NullMarked;

/**
 * Loader for proof obligation arises from dependency contracts.
 *
 * @author Alexander Weigl
 */
@NullMarked
public class DependencyContractPOLoader implements ProofObligationLoader {
    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link de.uka.ilkd.key.proof.init.InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     */
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties) {
        String contractName = Objects.requireNonNull(properties.getString("contract"));
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
            throw new RuntimeException("Contract not found: " + baseContractName);
        } else {
            return new IPersistablePO.LoadedPOContainer(
                contract.createProofObl(initConfig, contract), proofNum);
        }
    }

    @Override
    public boolean handles(String identifier) {
        return DependencyContractPO.class.getName().equals(identifier)
                || DependencyContractPO.class.getSimpleName().equals(identifier)
                || DependencyContractPOLoader.class.getName().equals(identifier)
                || DependencyContractPOLoader.class.getSimpleName().equals(identifier);
    }
}
