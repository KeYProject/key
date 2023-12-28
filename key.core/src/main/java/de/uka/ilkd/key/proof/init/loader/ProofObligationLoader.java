package de.uka.ilkd.key.proof.init.loader;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.Configuration;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
public interface ProofObligationLoader {
    IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig, Configuration properties) throws Exception;

    boolean handles(String identifier);
}
