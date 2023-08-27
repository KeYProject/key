/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskStartedInfo.TaskKind;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

import org.key_project.util.collection.ImmutableList;

/**
 *
 * @author christoph scheben
 */
public abstract class SequentialOnLastGoalProofMacro extends SequentialProofMacro {

    /**
     * {@inheritDoc}
     *
     * <p>
     * The macros are always started on the last active goal (in contrast to the same goal as it is
     * done in the SequentialProofMacro).
     *
     * @throws InterruptedException if one of the wrapped macros is interrupted.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, final ProverTaskListener listener)
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
