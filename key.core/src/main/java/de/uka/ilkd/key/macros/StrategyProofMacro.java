/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.util.List;
import java.util.stream.Collectors;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.strategy.FocussedRuleApplicationManager;
import de.uka.ilkd.key.strategy.Strategy;

import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.ProverCore;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.util.collection.ImmutableList;


/**
 * The abstract class StrategyProofMacro can be used to define proof macros which use their own
 * strategy.
 *
 * In order to implement a {@link StrategyProofMacro}, override
 * {@link #createStrategy(Proof, PosInOccurrence)}.
 *
 * This class is aware of Position in occurrences and can also be applied to inner nodes. Both
 * {@link RuleApplicationManager} and {@link Strategy} are changed for the course of the
 * macro but are restored afterwards using a {@link ProverTaskListener}.
 *
 * @see ProverTaskListener
 * @see Strategy
 */
public abstract class StrategyProofMacro extends AbstractProofMacro {

    protected abstract Strategy<Goal> createStrategy(Proof proof, PosInOccurrence posInOcc);

    /**
     * {@inheritDoc}
     *
     * This macro can always be applied (does not change anything perhaps)
     *
     * TODO make this only applicable if it has an impact.
     *
     */
    @Override
    public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals,
            PosInOccurrence posInOcc) {
        return goals != null && !goals.isEmpty();
    }

    /**
     * Subclasses can use this method to do some postprocessing on the proof-object after the
     * strategy has finished.
     *
     * @param proof The proof object.
     */
    protected void doPostProcessing(Proof proof) {}

    /*
     * Set a new rule app manager similar to the focussed mode. Set a new strategy which only allows
     * for the named admitted rules. Then run automation mode and in the end reset the managers. and
     * the strategy.
     *
     * If the automation is interrupted, report the interruption as an exception.
     */
    @Override
    public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof,
            ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener)
            throws InterruptedException {
        if (goals == null || goals.isEmpty()) {
            // should not happen, because in this case canApplyTo returns
            // false
            return null;
        }
        List<Node> nodes = goals.stream().map(Goal::node).collect(Collectors.toList());

        final GoalChooser goalChooser =
            proof.getInitConfig().getProfile().getSelectedGoalChooserBuilder().create();
        final ProverCore applyStrategy = new ApplyStrategy(goalChooser);
        final ImmutableList<Goal> ignoredOpenGoals = setDifference(proof.openGoals(), goals);

        //
        // The observer to handle the progress bar
        final ProofMacroListener pml =
            new ProgressBarListener(goals.size(), getMaxSteps(proof), listener);
        applyStrategy.addProverTaskObserver(pml);
        // add a focus manager if there is a focus
        if (posInOcc != null) {
            RuleApplicationManager realManager;
            FocussedRuleApplicationManager manager;
            for (Goal goal : goals) {
                realManager = goal.getRuleAppManager();
                realManager.clearCache();
                manager = new FocussedRuleApplicationManager(realManager, goal, posInOcc);
                goal.setRuleAppManager(manager);
            }
        }

        // set a new strategy.
        Strategy oldStrategy = proof.getActiveStrategy();
        proof.setActiveStrategy(createStrategy(proof, posInOcc));

        ProofMacroFinishedInfo info;
        try {
            // find the relevant goals
            // and start
            applyStrategy.start(proof, goals);
            synchronized (applyStrategy) { // wait for applyStrategy to finish its last rule
                                           // application
                if (applyStrategy.hasBeenInterrupted()) { // reraise interrupted exception if
                                                          // necessary
                    throw new InterruptedException();
                }
            }
        } finally {
            // this resets the proof strategy and the managers after the automation
            // has run
            for (final Goal openGoal : proof.openGoals()) {
                RuleApplicationManager manager = openGoal.getRuleAppManager();
                // touch the manager only if necessary
                if (manager instanceof FocussedRuleApplicationManager) {
                    manager = ((FocussedRuleApplicationManager) manager).rootManager;
                    manager.clearCache();
                    openGoal.setRuleAppManager(manager);
                }
            }
            final ImmutableList<Goal> resultingGoals =
                setDifference(proof.openGoals(), ignoredOpenGoals);
            info = new ProofMacroFinishedInfo(this, resultingGoals,
                nodes);
            proof.setActiveStrategy(oldStrategy);
            doPostProcessing(proof);
            applyStrategy.removeProverTaskObserver(pml);
        }
        return info;
    }

    private static ImmutableList<Goal> setDifference(ImmutableList<Goal> goals1,
            ImmutableList<Goal> goals2) {
        ImmutableList<Goal> difference = goals1;
        for (Goal goal : goals2) {
            difference = difference.removeFirst(goal);
        }
        return difference;
    }
}
