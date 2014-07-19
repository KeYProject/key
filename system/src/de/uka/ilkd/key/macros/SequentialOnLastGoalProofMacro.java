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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

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
    public ProofMacroFinishedInfo applyTo(KeYMediator mediator,
                                          ImmutableList<Goal> goals,
                                          PosInOccurrence posInOcc,
                                          final ProverTaskListener listener) throws InterruptedException {
        ProofMacroFinishedInfo info = new ProofMacroFinishedInfo(this, goals);
        for (final ProofMacro macro : getProofMacros()) {
            // (here we do not reverse to original node)
            if (macro.canApplyTo(mediator, goals, posInOcc)) {
                final ProverTaskListener pml = new ProofMacroListener(macro, listener);
                pml.taskStarted(macro.getName(), 0);
                synchronized(macro) {
                    // wait for macro to terminate
                    info = macro.applyTo(mediator, goals, posInOcc, pml);
                }
                pml.taskFinished(info);
                info = new ProofMacroFinishedInfo(this, info);
                goals = info.getGoals();
                // after the first macro the posInOcc does not match any more,
                // because we changed the goal / node
                posInOcc = null;
            }
        }
        return info;
    }
}