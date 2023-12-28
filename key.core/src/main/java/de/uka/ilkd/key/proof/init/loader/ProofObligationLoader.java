/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init.loader;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.settings.Configuration;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
public interface ProofObligationLoader {
    IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig, Configuration properties)
            throws Exception;

    boolean handles(String identifier);
}
