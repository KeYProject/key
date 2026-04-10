/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.macros.AlternativeMacro;
import de.uka.ilkd.key.macros.ProofMacro;

public class StartAuxiliaryComputationMacro extends AlternativeMacro {

    @Override
    public String getName() {
        return "Start auxiliary computation for self-composition proofs";
    }

    @Override
    public String getCategory() {
        return "Auxiliary Computation";
    }

    @Override
    public String getDescription() {
        return "In order to increase the efficiency of self-composition "
            + "proofs, this macro starts a side calculation which does "
            + "the symbolic execution only once. The result is "
            + "instantiated twice with the variable to be used in the "
            + "two executions of the self-composition.";
    }

    @Override
    public String getScriptCommandName() {
        return "aux-start";
    }

    @Override
    protected ProofMacro[] createProofMacroArray() {
        return new ProofMacro[] { new StartAuxiliaryMethodComputationMacro(),
            new StartAuxiliaryLoopComputationMacro(), new StartAuxiliaryBlockComputationMacro() };
    }

}
