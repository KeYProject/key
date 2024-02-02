/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.taclettranslation.lemma;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;
import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (29.12.23)
 */
@NullMarked
public class TacletProofObligationInputLoader implements ProofObligationLoader {
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties) {
        String tacletName = properties.getString(IPersistablePO.PROPERTY_NAME);
        // This string is parsed by "proveRules.pl"
        if (java.awt.GraphicsEnvironment.isHeadless()) {
            TacletProofObligationInput.LOGGER.info("Proof obligation for taclet: {}", tacletName);
        }
        TacletProofObligationInput proofOblInput =
            new TacletProofObligationInput(tacletName, initConfig);
        proofOblInput.setLoadInfo(properties);
        return new IPersistablePO.LoadedPOContainer(proofOblInput);
    }

    @Override
    public boolean handles(String identifier) {
        return TacletProofObligationInput.class.getSimpleName().equals(identifier)
                || TacletProofObligationInput.class.getName().equals(identifier)
                || getClass().getName().equals(identifier)
                || getClass().getSimpleName().equals(identifier);
    }
}
