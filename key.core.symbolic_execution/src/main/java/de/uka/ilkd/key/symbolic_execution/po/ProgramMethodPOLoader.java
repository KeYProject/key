/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.po;

import java.io.IOException;

import de.uka.ilkd.key.proof.init.IPersistablePO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;
import org.jspecify.annotations.NullMarked;

import static de.uka.ilkd.key.proof.init.AbstractPO.getName;
import static de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO.*;

@NullMarked
public class ProgramMethodPOLoader implements ProofObligationLoader {
    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     */
    @Override
    public IPersistablePO.LoadedPOContainer loadFrom(InitConfig initConfig,
            Configuration properties)
            throws IOException {
        return new IPersistablePO.LoadedPOContainer(new ProgramMethodPO(initConfig,
            getName(properties),
            ProgramMethodPO.getProgramMethod(initConfig, properties), getPrecondition(properties),
            isAddUninterpretedPredicate(properties), isAddSymbolicExecutionLabel(properties)));
    }

    @Override
    public boolean handles(String identifier) {
        return ProgramMethodPOLoader.class.getSimpleName().equals(identifier)
                || ProgramMethodPOLoader.class.getName().equals(identifier)
                || ProgramMethodPO.class.getSimpleName().equals(identifier)
                || ProgramMethodPO.class.getName().equals(identifier);
    }
}
