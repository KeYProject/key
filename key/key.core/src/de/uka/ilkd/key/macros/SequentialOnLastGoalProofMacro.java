// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.macros;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskStartedInfo.TaskKind;

/**
 *
 * @author christoph scheben
 */
public abstract class SequentialOnLastGoalProofMacro extends SequentialProofMacro {

    /**
     * {@inheritDoc}
     *
     * <p>
     * The macros are always started on the last active goal (in contrast
     * to the same goal as it is done in the SequentialProofMacro).
     *
     * @throws InterruptedException
     *             if one of the wrapped macros is interrupted.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic,
                                          Proof proof,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          final ProverTaskListener listener) throws InterruptedException, Exception {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        for (final ProofMacro macro : getProofMacros()) {
            // (here we do not reverse to original node)
            if (macro.canApplyTo(proof, goals, posInOcc)) {
                final ProverTaskListener pml = new ProofMacroListener(macro, listener);
                pml.taskStarted(new DefaultTaskStartedInfo(TaskKind.Macro, macro.getName(), 0));
                synchronized(macro) {
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