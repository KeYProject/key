/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd.po;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;
import org.jspecify.annotations.NullMarked;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Loader for proof obligation arises from well definedness.
 *
 * @author Alexander Weigl
 * @version 1 (29.12.23)
 */
@NullMarked
public class WellDefinednessPOLoader implements ProofObligationLoader {
    private static final Logger LOGGER = LoggerFactory.getLogger(WellDefinednessPOLoader.class);

    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already loaded {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     */
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig, Configuration properties) {
        String contractName = properties.getString("wd check");
        final Contract contract =
                initConfig.getServices().getSpecificationRepository().getContractByName(contractName);
        if (contract == null) {
            LOGGER.error("Contract {} not found.", contractName);
            var c = initConfig.getServices().getSpecificationRepository();
            LOGGER.info("Available contracts: ");
            for (var contr : c.getAllContracts()) {
                LOGGER.info("Name:{}, Display: {}", contr.getName(), contr.getDisplayName());
            }

            throw new RuntimeException("Contract not found: " + contractName);
        } else {
            final ProofOblInput po = contract.createProofObl(initConfig);
            return new IPersistablePO.LoadedPOContainer(po);
        }
    }

    @Override
    public boolean handles(String identifier) {
        return WellDefinednessPO.class.getSimpleName().equals(identifier)
                || WellDefinednessPO.class.getName().equals(identifier)
                || WellDefinednessPOLoader.class.getSimpleName().equals(identifier)
                || WellDefinednessPOLoader.class.getName().equals(identifier);
    }
}
