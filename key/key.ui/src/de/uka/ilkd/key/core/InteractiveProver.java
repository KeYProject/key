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
package de.uka.ilkd.key.core;

import java.util.concurrent.CancellationException;
import java.util.concurrent.ExecutionException;

import javax.swing.SwingUtilities;
import javax.swing.SwingWorker;

import org.key_project.utils.collection.ImmutableList;
import org.key_project.utils.collection.ImmutableSLList;

import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.gui.notification.events.GeneralInformationEvent;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.ApplyStrategy;
import de.uka.ilkd.key.proof.ApplyStrategy.ApplyStrategyInfo;
import de.uka.ilkd.key.proof.DepthFirstGoalChooserBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.TaskFinishedInfo;
import de.uka.ilkd.key.strategy.AutomatedRuleApplicationManager;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.util.Debug;

public class InteractiveProver implements InterruptListener {

    /**
     * the proof the interactive prover works on
     */
    private Proof proof;

    /**
     * the central strategy processor including GUI signalling
     */
    private final ApplyStrategy applyStrategy;
    private final ProverTaskListener focussedAutoModeTaskListener
            = new FocussedAutoModeTaskListener();


    /**
     * the mediator
     */
    private final KeYMediator mediator;

    private AutoModeWorker worker;

    /**
     * creates a new interactive prover object
     */
    public InteractiveProver(final KeYMediator mediator) {
        /* listens to the current selected proof and node */
        this.mediator = mediator;
        mediator.addKeYSelectionListener(new InteractiveProverKeYSelectionListener());

        mediator.getProfile().setSelectedGoalChooserBuilder(DepthFirstGoalChooserBuilder.NAME);//XXX

        applyStrategy =
                new ApplyStrategy(mediator.getProfile().getSelectedGoalChooserBuilder().create());
        applyStrategy.addProverTaskObserver(mediator().getUI());

        if (mediator.getAutoSaver() != null) {
            applyStrategy.addProverTaskObserver(mediator.getAutoSaver());
        }
    }

    /**
     * returns the KeYMediator
     */
    KeYMediator mediator() {
        return mediator;
    }

    /**
     * sets up a new proof
     *
     * @param p a Proof that contains the root of the proof tree
     */
    public void setProof(Proof p) {
        proof = p;
        if (mediator.getAutoSaver() != null) {
            mediator.getAutoSaver().setProof(p);
        }
    }

    private long getTimeout() {
        return mediator().getAutomaticApplicationTimeout();
    }

    /**
     * returns the proof the interactive prover is working on
     *
     * @return the proof the interactive prover is working on
     */
    public Proof getProof() {
        return proof;
    }

    /**
     * starts the execution of rules with active strategy. The strategy will
     * only be applied on the goals of the list that is handed over and on the
     * new goals an applied rule adds
     */
    public void startAutoMode(ImmutableList<Goal> goals) {
        if (goals.isEmpty()) {
            mediator().notify(new GeneralInformationEvent("No enabled goals available."));
            return;
        }
        worker = new AutoModeWorker(goals);
        mediator().stopInterface(true);
        mediator().setInteractive(false);
        worker.execute();
    }

    /**
     * stops the execution of rules
     */
    @Override
    public void interruptionPerformed() {
        if (worker != null) {
            worker.cancel(true);
        }
    }

    /**
     * starts the execution of rules with active strategy. Restrict the
     * application of rules to a particular goal and (for
     * <code>focus!=null</code>) to a particular subterm or subformula of that
     * goal
     */
    public void startFocussedAutoMode(PosInOccurrence focus, Goal goal) {
        applyStrategy.addProverTaskObserver(focussedAutoModeTaskListener);

        if (focus != null) {
            // exchange the rule app manager of that goal to filter rule apps

            final AutomatedRuleApplicationManager realManager = goal.getRuleAppManager();
            goal.setRuleAppManager(null);
            final AutomatedRuleApplicationManager focusManager
                    = new FocussedRuleApplicationManager(realManager, goal, focus);
            goal.setRuleAppManager(focusManager);
        }

        startAutoMode(ImmutableSLList.<Goal>nil().prepend(goal));
    }

    private void finishFocussedAutoMode() {
        applyStrategy.removeProverTaskObserver(focussedAutoModeTaskListener);

        for (final Goal goal : proof.openGoals()) {
            // remove any filtering rule app managers that are left in the proof
            // goals
            if (goal.getRuleAppManager() instanceof FocussedRuleApplicationManager) {
                final AutomatedRuleApplicationManager focusManager
                        = (AutomatedRuleApplicationManager) goal.getRuleAppManager();
                goal.setRuleAppManager(null);
                final AutomatedRuleApplicationManager realManager
                        = focusManager.getDelegate();
                realManager.clearCache();
                goal.setRuleAppManager(realManager);
            }
        }
    }

    private final class FocussedAutoModeTaskListener implements ProverTaskListener {

        @Override
        public void taskStarted(String message, int size) {
        }

        @Override
        public void taskProgress(int position) {
        }

        @Override
        public void taskFinished(TaskFinishedInfo info) {
            SwingUtilities.invokeLater(new Runnable() {
                @Override
                public void run() {
                    finishFocussedAutoMode();
                }
            });
        }
    }

    /**
     * listener to KeYSelection Events in order to be informed if the current
     * proof changed
     */
    private class InteractiveProverKeYSelectionListener
            implements KeYSelectionListener {

        /**
         * focused node has changed
         */
        @Override
        public void selectedNodeChanged(KeYSelectionEvent e) {
        }

        /**
         * the selected proof has changed (e.g. a new proof has been loaded)
         */
        @Override
        public void selectedProofChanged(KeYSelectionEvent e) {
            Debug.out("InteractiveProver: initialize with new proof");
            Proof newProof = e.getSource().getSelectedProof();
            setProof(newProof); // this is null-safe
        }

    }

    /**
     * The purpose is to reset the interactiveProver to prevent memory leaking.
     * This method is used, e.g., by
     * {@code TaskTree.removeTaskWithoutInteraction}. An alternative would be to
     * reset the InteractiveProver in
     * {@code InteractiveProverKeYSelectionListener.selectedProofChanged} but
     * there we don't know whether the proof has been abandoned or not.
     *
     * @author gladisch
     */
    public void clear() {
        if (applyStrategy != null) {
            applyStrategy.clear();
        }
        if (proof != null) {
            proof.clearAndDetachRuleAppIndexes();
            proof = null;
        }
        //probably more clean up has to be done here.
    }

    /* <p>
     * Invoking start() on the SwingWorker causes a new Thread
     * to be created that will call construct(), and then
     * finished().  Note that finished() is called even if
     * the worker is interrupted because we catch the
     * InterruptedException in doWork().
     * </p>
     * <p>
     * <b>Attention:</b> Before this thread is started it is required to
     * freeze the MainWindow via
     * {@code
     * mediator().stopInterface(true);
     *   mediator().setInteractive(false);
     * }. The thread itself unfreezes the UI when it is finished.
     * </p>
     */
    private class AutoModeWorker extends SwingWorker<ApplyStrategyInfo, Object> {

        private final ImmutableList<Goal> goals;

        public AutoModeWorker(final ImmutableList<Goal> goals) {
            this.goals = goals;
        }

        @Override
        protected void done() {
            try {
                get();
            } catch (final InterruptedException exception) {
                notifyException(exception);
            } catch (final ExecutionException exception) {
                notifyException(exception);
            } catch (final CancellationException exception) {
                // when the user canceled it's not an error
            }

            synchronized(applyStrategy) {
                // make it possible to free memory and falsify the isAutoMode() property
                worker = null;
                // wait for apply Strategy to terminate
                mediator().setInteractive(true);
                mediator().startInterface(true);
            }
        }

        private void notifyException(final Exception exception) {
            mediator().notify(new GeneralFailureEvent("An exception occurred during"
                    + " strategy execution.\n Exception:" + exception));
        }

        @Override
        protected ApplyStrategyInfo doInBackground() throws Exception {
            boolean stopMode = proof.getSettings().getStrategySettings()
                    .getActiveStrategyProperties().getProperty(
                            StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);
            return applyStrategy.start(proof, goals, mediator().getMaxAutomaticSteps(),
                    getTimeout(), stopMode);
        }
    }
}
