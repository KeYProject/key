/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.Contract;
import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (29.12.23)
 */
@NullMarked
public class WellDefinednessPOLoader implements ProofObligationLoader {
    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     */
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties) {
        String contractName = properties.getString("wd check");
        final Contract contract =
            initConfig.getServices().getSpecificationRepository().getContractByName(contractName);
        if (contract == null) {
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
