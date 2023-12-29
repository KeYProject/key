package de.uka.ilkd.key.taclettranslation.lemma;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;

/**
 * @author Alexander Weigl
 * @version 1 (29.12.23)
 */
public class TacletProofObligationInputLoader implements ProofObligationLoader {
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig, Configuration properties) {
        String tacletName = properties.getString(IPersistablePO.PROPERTY_NAME);
        // This string is parsed by "proveRules.pl"
        if (java.awt.GraphicsEnvironment.isHeadless()) {
            TacletProofObligationInput.LOGGER.info("Proof obligation for taclet: {}", tacletName);
        }
        TacletProofObligationInput proofOblInput = new TacletProofObligationInput(tacletName, initConfig);
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
