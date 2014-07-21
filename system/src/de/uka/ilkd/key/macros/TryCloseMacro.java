// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.macros;


import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.ApplyStrategy;
import de.uka.ilkd.key.gui.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.gui.DefaultTaskFinishedInfo;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IGoalChooser;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.ui.UserInterface;

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
public class TryCloseMacro extends AbstractProofMacro {

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
    public boolean canApplyTo(KeYMediator mediator, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
        return true;
    }

    /*
     * Run the automation on the goal. Retreat if not successful.
     */
    @Override
    public void applyTo(KeYMediator mediator, ImmutableList<Goal> goals, PosInOccurrence posInOcc,
                        ProverTaskListener listener) throws InterruptedException {
        //
        // create the rule application engine
        final IGoalChooser chooser =
                mediator.getProfile().getSelectedGoalChooserBuilder().create();
        final ApplyStrategy applyStrategy =
                new ApplyStrategy(chooser, finishAfterMacro());
        final Proof proof = mediator.getInteractiveProver().getProof();

        //
        // The observer to handle the progress bar
        TaskObserver taskObserver = new TaskObserver(mediator.getUI(), finishAfterMacro());
        taskObserver.setNumberGoals(goals.size());

        //
        // set the max number of steps if given
        int oldNumberOfSteps = mediator.getMaxAutomaticSteps();
        if(numberSteps > 0) {
            mediator.setMaxAutomaticSteps(numberSteps);
            taskObserver.setNumberSteps(numberSteps);
        } else {
            taskObserver.setNumberSteps(oldNumberOfSteps);
        }

        applyStrategy.addProverTaskObserver(taskObserver);

        //
        // inform the listener
        int goalsClosed = 0;
        long time = 0;
        int appliedRules = 0;

        //
        // start actual autoprove
        try {
            for (Goal goal : goals) {
                Node node = goal.node();
                ApplyStrategyInfo result =
                        applyStrategy.start(proof, ImmutableSLList.<Goal>nil().prepend(goal));

                // retreat if not closed
                if(!node.isClosed()) {
                    proof.pruneProof(node);
                } else {
                    goalsClosed++;
                }

                // update statistics
                time += result.getTime();
                appliedRules += result.getAppliedRuleApps();

                synchronized(applyStrategy) { // wait for applyStrategy to finish it last rule application
                   if(applyStrategy.hasBeenInterrupted()) { // only now reraise the interruption exception
                      throw new InterruptedException();
                   }
                }
            }
        } finally {
            // reset the old number of steps
            mediator.setMaxAutomaticSteps(oldNumberOfSteps);
            // inform the listener
            taskObserver.allTasksFinished(proof, time, appliedRules, goalsClosed);
        }
    }

    /**
     * This observer acts as intermediate instance between the reports by the
     * strategy and the UI reporting progress.
     *
     * The number of total steps is computed and all local reports are
     * translated in termini of the total number of steps such that a continuous
     * progress is reported.
     *
     * fixes #1356
     */
    private static class TaskObserver implements ProverTaskListener {

        private int numberGoals;
        private int numberSteps;
        private final ProverTaskListener backListener;
        private final boolean finishAfterMacro;
        private int completedGoals;

        public TaskObserver(ProverTaskListener backListener,
                            boolean finishAfterMacro) {
            this.backListener = backListener;
            this.finishAfterMacro = finishAfterMacro;
        }

        @Override
        public void taskStarted(String message, int size) {
            assert size == numberSteps;
            String suffix = " [" + (completedGoals + 1) + "/" + numberGoals + "]";
            backListener.taskStarted(message + suffix, numberGoals * numberSteps);
            backListener.taskProgress(completedGoals * numberSteps);
        }

        @Override
        public void taskProgress(int position) {
            backListener.taskProgress(completedGoals * numberSteps + position);
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            completedGoals ++;
        }

        public void setNumberGoals(int numberGoals) {
            this.numberGoals = numberGoals;
        }

        public void setNumberSteps(int numberSteps) {
            this.numberSteps = numberSteps;
        }

        private void allTasksFinished(Proof proof, long time, int appliedRules, int closedGoals) {
			TaskFinishedInfo info =
					new DefaultTaskFinishedInfo(this, null, proof, time,
                                                appliedRules, closedGoals);
			assert backListener instanceof UserInterface;
			final UserInterface ui = (UserInterface)backListener;
			if (finishAfterMacro) {
				backListener.taskFinished(info);
            } else if (!ui.macroChosen()) {
                ui.finish(proof);
            }
        }
    }
}