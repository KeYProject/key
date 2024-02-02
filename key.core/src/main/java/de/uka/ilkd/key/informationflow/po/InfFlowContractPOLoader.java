/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;
import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
@NullMarked
public class InfFlowContractPOLoader implements ProofObligationLoader {

    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     */
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties) {
        final String contractName = properties.getString("contract");
        final Contract contract =
            initConfig.getServices().getSpecificationRepository().getContractByName(contractName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + contractName);
        } else {
            return new IPersistablePO.LoadedPOContainer(contract.createProofObl(initConfig), 0);
        }
    }

    @Override
    public boolean handles(String identifier) {
        return InfFlowContractPO.class.getName().equals(identifier)
                || InfFlowContractPO.class.getSimpleName().equals(identifier)
                || InfFlowContractPOLoader.class.getName().equals(identifier)
                || InfFlowContractPOLoader.class.getSimpleName().equals(identifier);
    }
}
