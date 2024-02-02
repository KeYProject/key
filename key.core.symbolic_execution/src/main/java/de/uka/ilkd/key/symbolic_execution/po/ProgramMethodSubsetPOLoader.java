/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.po;

import java.io.IOException;

import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.proof.init.loader.ProofObligationLoader;
import de.uka.ilkd.key.settings.Configuration;
import org.jspecify.annotations.NullMarked;

/**
 * @author Alexander Weigl
 * @version 1 (28.12.23)
 */
@NullMarked
public class ProgramMethodSubsetPOLoader implements ProofObligationLoader {
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
            Configuration properties) throws IOException {
        return new IPersistablePO.LoadedPOContainer(
            new ProgramMethodSubsetPO(initConfig, AbstractPO.getName(properties),
                ProgramMethodPO.getProgramMethod(initConfig, properties),
                ProgramMethodPO.getPrecondition(properties),
                ProgramMethodSubsetPO.getStartPosition(properties),
                ProgramMethodSubsetPO.getEndPosition(properties),
                AbstractOperationPO.isAddUninterpretedPredicate(properties),
                AbstractOperationPO.isAddSymbolicExecutionLabel(properties)));
    }

    @Override
    public boolean handles(String identifier) {
        return ProgramMethodSubsetPO.class.getName().equals(identifier)
                || ProgramMethodSubsetPO.class.getSimpleName().equals(identifier)
                || getClass().getName().equals(identifier)
                || getClass().getSimpleName().equals(identifier);
    }
}
