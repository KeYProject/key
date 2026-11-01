/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.engine.TaskStartedInfo.TaskKind;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 *
 * @author christoph scheben
 */
@NullMarked
public abstract class SequentialOnLastGoalProofMacro extends SequentialProofMacro {

    /**
     * {@inheritDoc}
     *
     * <p>
     * The macros are always started on the last active goal (in contrast to the same goal as it is
     * done in the SequentialProofMacro).
     *
     * <p>
     * The finished info of a wrapped macro may carry no proof; by construction of
     * {@link ProofMacroFinishedInfo}, this happens exactly when the macro finished on an empty
     * goal list (no open goals remain). The remaining macros are then skipped, as the
     * {@link ProofMacro#canApplyTo} implementations of this macro family decide on the goal list
     * first and never dereference the absent proof; the assignment of the (nullable) proof of the
     * wrapped info to the non-null parameter is suppressed with a scoped key.
     *
     * @throws InterruptedException if one of the wrapped macros is interrupted.
     */
    @SuppressWarnings("nullness:assignment.type.incompatible")
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, @Nullable PosInOccurrence posInOcc,
            final @Nullable ProverTaskListener listener)
            throws Exception {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        for (final ProofMacro macro : getProofMacros()) {
            // (here we do not reverse to original node)
            if (macro.canApplyTo(proof, goals, posInOcc)) {
                final ProverTaskListener pml = new ProofMacroListener(macro.getName(), listener);
                pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
                synchronized (macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(uic, proof, goals, posInOcc, pml);
                }
                pml.taskFinished(info);
                info = new ProofMacroFinishedInfo(this, info);
                goals = info.getGoals();
                proof = info.getProof();
                // after the first macro the posInOcc does not match any more,
                // because we changed the goal / node
                posInOcc = null;
            }
        }
        return info;
    }
}
