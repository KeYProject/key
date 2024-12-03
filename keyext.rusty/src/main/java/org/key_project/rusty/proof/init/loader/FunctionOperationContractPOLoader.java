/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init.loader;

import java.io.IOException;

import org.key_project.rusty.proof.init.FunctionalOperationContractPO;
import org.key_project.rusty.proof.init.IPersistablePO;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.ProofOblInput;
import org.key_project.rusty.settings.Configuration;
import org.key_project.rusty.speclang.Contract;

import org.jspecify.annotations.NullMarked;

/**
 * Loader for proof obligation arises by function operation contract.
 *
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
@NullMarked
public class FunctionOperationContractPOLoader implements ProofObligationLoader {
    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already loaded {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties) throws Exception {
        String contractName = properties.getString("contract");
        String baseContractName;
        baseContractName = contractName;
        final Contract contract = initConfig.getServices().getSpecificationRepository()
                .getContractByName(baseContractName);
        if (contract == null) {
            throw new IllegalStateException("Contract not found: " + baseContractName);
        } else {
            final ProofOblInput po = contract.createProofObl(initConfig);
            return new IPersistablePO.LoadedPOContainer(po);
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
