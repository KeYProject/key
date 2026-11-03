/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.macros;

import de.uka.ilkd.key.informationflow.po.AbstractInfFlowPO;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.macros.AlternativeMacro;
import de.uka.ilkd.key.macros.DoWhileFinallyMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.SequentialOnLastGoalProofMacro;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofOblInput;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class FullInformationFlowAutoPilotMacro extends DoWhileFinallyMacro {

    /**
     * The number of proof steps that should be run by the {@link TryCloseMacro} before retracting.
     * This overrides the strategy setting if set to a value greater or equal to 0.
     */
    private static final int NUMBER_OF_TRY_STEPS = -1;

    @Override
    public String getName() {
        return "Full Information Flow Auto Pilot";
    }

    @Override
    public String getCategory() {
        return "Information Flow";
    }

    @Override
    public String getScriptCommandName() {
        return "infflow-autopilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Search exhaustively for applicable position, then"
            + "<li>Start auxiliary computation" + "<li>Finish symbolic execution"
            + "<li>Try to close as many goals as possible" + "<li>Apply macro recursively"
            + "<li>Finish auxiliary computation" + "<li>Use information flow contracts"
            + "<li>Try to close as many goals as possible</ol>";
    }

    @Override
    protected ProofMacro getProofMacro() {
        final SequentialProofMacro stateExpansionAndCloseMacro = new SequentialProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] { new StateExpansionAndInfFlowContractApplicationMacro(),
                    new TryCloseMacro(NUMBER_OF_TRY_STEPS) };
            }

            @Override
            public String getName() { return ""; }

            @Override
            public String getCategory() { return null; }

            @Override
            public String getDescription() { return "Anonymous Macro"; }
        };

        final SequentialProofMacro finishMainCompMacro = new SequentialOnLastGoalProofMacro() {
            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] { new FinishAuxiliaryComputationMacro(),
                    stateExpansionAndCloseMacro };
            }

            @Override
            public String getName() { return ""; }

            @Override
            public String getCategory() { return null; }

            @Override
            public String getDescription() { return "Anonymous Macro"; }
        };

        return new AlternativeMacro() {
            @Override
            public String getName() { return ""; }

            @Override
            public String getCategory() { return null; }

            @Override
            public String getDescription() { return "Anonymous Macro"; }

            @Override
            protected ProofMacro[] createProofMacroArray() {
                return new ProofMacro[] { new AuxiliaryComputationAutoPilotMacro(),
                    finishMainCompMacro };
            }
        };
    }

    @Override
    protected ProofMacro getAltProofMacro() {
        return new SkipMacro();
    }

    @Override
    protected boolean getCondition() {
        return true;
    }


    /**
     * {@inheritDoc}
     *
     * <p>
     * This compound macro is applicable if and only if the first macro is applicable. If there is
     * no first macro, this is not applicable.
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence posInOcc) {
        if (proof == null) {
            return false;
        }
        final Services services = proof.getServices();
        if (services == null) {
            return false;
        }
        final ProofOblInput poForProof =
            services.getSpecificationRepository().getProofOblInput(proof);
        return (poForProof instanceof AbstractInfFlowPO)
                && canApplyToSuper(proof, goals, posInOcc);
    }


    /**
     * Deliberately forwards the position of the occurrence to the base
     * implementation even when it is {@code null}: at macro level the position
     * is not meaningful and the base implementations only consult the goals
     * and forward the position unchanged, never dereferencing it. Requiring a
     * non-null position here would change the historical applicability of this
     * macro; the base signature is not nullness-annotated and cannot be
     * widened from this module.
     */
    @SuppressWarnings("nullness:argument.type.incompatible")
    private boolean canApplyToSuper(Proof proof, ImmutableList<Goal> goals,
            @Nullable PosInOccurrence posInOcc) {
        return super.canApplyTo(proof, goals, posInOcc);
    }
}
