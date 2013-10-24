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

package de.uka.ilkd.key.gui.macros;

import java.awt.event.InputEvent;
import java.awt.event.KeyEvent;

import javax.swing.KeyStroke;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * The Class TryCloseMacro tries to close goals. Goals are either closed or left
 * untouched.
 *
 * This uses the code provided by Michael Kirsten in
 * {@link InteractiveProver$AutoWorker}.
 *
 * The number of autosteps may be temporarily altered for this macro.
 *
 * @author mattias ulbrich
 */
public class TryCloseMacro implements ProofMacro {

    /**
     * The max number of steps to be applied.
     * A value of -1 means no changes.
     */
    private final int numberSteps;

    /**
     * Instantiates a new try close macro.
     * No changes to the max number of steps.
     */
    public TryCloseMacro() {
        this.numberSteps = -1;
    }

    /**
     * Instantiates a new try close macro.
     *
     * @param numberSteps
     *            the max number of steps. -1 means no change.
     */
    public TryCloseMacro(int numberSteps) {
        this.numberSteps = numberSteps;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getName()
     */
    @Override
    public String getName() {
        return "Close provable goals below";
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.gui.macros.ProofMacro#getDescription()
     */
    @Override
    public String getDescription() {
        return "Closes closable goals, leave rest untouched (see settings AutoPrune). " +
                "Applies only to goals beneath the selected node.";
    }

    /*
     * This macro is always applicable.
     */
    @Override
    public boolean canApplyTo(KeYMediator mediator, PosInOccurrence posInOcc) {
        return true;
    }

    /* 
     * Run the automation on the goals. Retreat if not successful.
     */
    @Override 
    public void applyTo(KeYMediator mediator, PosInOccurrence posInOcc,
            ProverTaskListener listener) throws InterruptedException {

        //
        // create the rule application engine
        final ApplyStrategy applyStrategy = 
                new ApplyStrategy(mediator.getProfile().getSelectedGoalChooserBuilder().create());

        final Proof proof = mediator.getInteractiveProver().getProof();

        //
        // find the targets
        Node invokedNode = mediator.getSelectedNode();
        ImmutableList<Goal> enabledGoals = proof.getSubtreeEnabledGoals(invokedNode);

        //
        // set the max number of steps if given
        int oldNumberOfSteps = mediator.getMaxAutomaticSteps();
        if(numberSteps > 0) {
            mediator.setMaxAutomaticSteps(numberSteps);
        }
        
        // 
        // inform the listener
        int goalsTotal = enabledGoals.size();
        int goalsClosed = 0;
        int goalsDone = 0;
        long time = 0;
        int appliedRules = 0;
        fireStart(listener, goalsTotal);

        //
        // start actual autoprove
        try {
            for (Goal goal : enabledGoals) {
                Node node = goal.node();
                ApplyStrategyInfo result = 
                        applyStrategy.start(proof, ImmutableSLList.<Goal>nil().prepend(goal));

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
                } else {
                    goalsClosed ++;
                }

                // update statistics
                goalsDone++;
                time += result.getTime();
                appliedRules += result.getAppliedRuleApps();

                // only now reraise the interruption exception
                if(applyStrategy.hasBeenInterrupted()) {
                    throw new InterruptedException();
                }
                
                fireProgress(listener, goalsDone);
            }
        } finally {
            // reset the old number of steps
            mediator.setMaxAutomaticSteps(oldNumberOfSteps);
            // inform the listener
            fireStop(listener, proof, time, appliedRules, goalsClosed);
        }

    }

    @Override
    public KeyStroke getKeyStroke () {
	return KeyStroke.getKeyStroke(KeyEvent.VK_C, InputEvent.SHIFT_DOWN_MASK);
    }

    private void fireStop(ProverTaskListener listener, Proof proof, long time, 
            int appliedRules, int closedGoals) {
        if(listener != null) {
            listener.taskFinished(
                    new DefaultTaskFinishedInfo(this, null, proof, 
                            time, appliedRules, closedGoals));
        }
    }

    private void fireStart(ProverTaskListener ptl, int numberGoals) {
        if(ptl != null) {
            ptl.taskStarted("Trying to close " + numberGoals +" open goals", numberGoals);
        }
    }

    private void fireProgress(ProverTaskListener ptl, int steps) {
        if (ptl != null) {
            ptl.taskProgress(steps);
        }
    }

}
