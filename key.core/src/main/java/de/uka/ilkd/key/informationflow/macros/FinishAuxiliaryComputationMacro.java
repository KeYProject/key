/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.macros.AlternativeMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import org.jspecify.annotations.NonNull;

public class FinishAuxiliaryComputationMacro extends AlternativeMacro {

    @Override
    public @NonNull String getName() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getCategory() {
        return "Auxiliary Computation";
    }

    @Override
    public @NonNull String getDescription() {
        return "Finish auxiliary computation";
    }

    @Override
    public @NonNull String getScriptCommandName() {
        return "aux-finish";
    }

    @Override
    protected ProofMacro @NonNull [] createProofMacroArray() {
        return new ProofMacro[] { new FinishAuxiliaryMethodComputationMacro(),
            new FinishAuxiliaryLoopComputationMacro(), new FinishAuxiliaryBlockComputationMacro() };
    }
}
