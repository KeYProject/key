/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SequentialOnLastGoalProofMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;


/**
 *
 * @author christoph scheben
 */
public class AuxiliaryComputationAutoPilotMacro extends ExhaustiveProofMacro {

    @Override
    public @NonNull String getName() {
        return "Auxiliary Computation Auto Pilot";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public @NonNull String getDescription() {
        return "<html><ol><li>Start auxiliary computation" + "<li>Finish symbolic execution"
            + "<li>Try to close as many goals as possible</ol>";
    }


    @Override
    @NonNull
    ProofMacro getProofMacro() {
        return new SequentialOnLastGoalProofMacro() {
            /**
             * The number of proof steps that should be run by the {@link TryCloseMacro} before
             * retracting. This overrides the strategy setting.
             */
            private final int NUMBER_OF_TRY_STEPS =
                Integer.getInteger("key.autopilot.closesteps", 1000);

            @Override
            public @NonNull String getName() { return ""; }

            @Override
            public String getCategory() { return null; }

            @Override
            public @NonNull String getDescription() { return "Anonymous Macro"; }

            @Override
            protected ProofMacro @NonNull [] createProofMacroArray() {
                // The FinishSymbolicExecutionMacro and the TryCloseMacro shall be
                // started at the same node. Therefore they are encapsulated in an
                // own (anonymous) SequentialProofMacro.
                SequentialProofMacro finishSymbExecAndTryToClose = new SequentialProofMacro() {
                    @Override
                    protected ProofMacro @NonNull [] createProofMacroArray() {
                        return new ProofMacro[] { new FinishSymbolicExecutionMacro(),
                            new TryCloseMacro(NUMBER_OF_TRY_STEPS) };
                    }

                    @Override
                    public @NonNull String getName() { return ""; }

                    @Override
                    public @Nullable String getCategory() { return null; }

                    @Override
                    public @NonNull String getDescription() { return "Anonymous Macro"; }
                };

                return new ProofMacro[] { new StartAuxiliaryComputationMacro(),
                    finishSymbExecAndTryToClose };
            }
        };
    }
}
