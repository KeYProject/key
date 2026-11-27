/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.prover.impl;


import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.prover.engine.*;
import org.key_project.prover.engine.impl.ApplyStrategyInfo;
import org.key_project.prover.engine.impl.DefaultProver;
import org.key_project.prover.engine.impl.DefaultTaskFinishedInfo;
import org.key_project.prover.engine.impl.DefaultTaskStartedInfo;
import org.key_project.prover.proof.ProofObject;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Applies rules in an automated fashion. The caller should ensure that the strategy runs in its own
 * thread
 * <a href="http://java.sun.com/products/jfc/tsc/articles/threads/threads2.html">Uses code by Hans
 * Muller and Kathy Walrath</a>
 *
 * @author Richard Bubel
 */
public class ApplyStrategy extends DefaultProver<Goal> {
    public static final Logger LOGGER = LoggerFactory.getLogger(ApplyStrategy.class);

    public static final AtomicLong PERF_GOAL_APPLY = new AtomicLong();

    /**
     * The default {@link GoalChooser} to choose goals to which rules are applied if the
     * {@link StrategySettings} of the proof provides no customized one.
     */
    private final GoalChooser<Goal> defaultGoalChooser;

    /** interrupted by the user? */
    private boolean autoModeActive = false;

    // Please create this object beforehand and re-use it.
    // Otherwise, the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(GoalChooser<Goal> defaultGoalChooser) {
        this.defaultGoalChooser = defaultGoalChooser;
    }

    private void init(Proof newProof, ImmutableList<Goal> goals, int maxSteps, long timeout) {
        this.proof = newProof;
        maxApplications = maxSteps;
        this.timeout = timeout;
        countApplied = 0;
        closedGoals = 0;
        cancelled = false;
        stopCondition =
            newProof.getSettings().getStrategySettings().getApplyStrategyStopCondition();
        assert stopCondition != null;
        goalChooser = getGoalChooserForProof(newProof);
        assert goalChooser != null;
        goalChooser.init(newProof, goals);
        setAutoModeActive(true);
        fireTaskStarted(
            new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Strategy, PROCESSING_STRATEGY,
                stopCondition.getMaximalWork(maxSteps, timeout)));
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public synchronized ApplyStrategyInfo<Goal> start(@NonNull ProofObject<Goal> proof,
            @NonNull Goal goal) {
        return start(proof, ImmutableList.<Goal>nil().prepend(goal));
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * org.key_project.util.collection.ImmutableList)
     */
    @Override
    public synchronized ApplyStrategyInfo<Goal> start(ProofObject<Goal> proof,
            @NonNull ImmutableList<Goal> goals) {
        final ProofSettings settings = ((Proof) proof).getSettings();
        StrategySettings stratSet = settings.getStrategySettings();
        return start(proof, goals, stratSet);
    }

    /*
     * (non-Javadoc)
     *
     */
    private synchronized ApplyStrategyInfo<Goal> start(ProofObject<Goal> p_proof,
            ImmutableList<Goal> goals, StrategySettings strategySettings) {
        final Proof proof = (Proof) p_proof;
        int maxSteps = strategySettings.getMaxSteps();
        long timeout = strategySettings.getTimeout();

        boolean stopAtFirstNonCloseableGoal = proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
        return start(proof, goals, maxSteps, timeout, stopAtFirstNonCloseableGoal);
    }

    private Proof proof() {
        return (Proof) proof;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * org.key_project.util.collection.ImmutableList, int, long, boolean)
     */
    @Override
    public synchronized ApplyStrategyInfo<Goal> start(@NonNull ProofObject<Goal> p_proof,
            @NonNull ImmutableList<Goal> goals,
            int maxSteps, long timeout, boolean stopAtFirstNonCloseableGoal) {
        final Proof proof = (Proof) p_proof;
        assert proof != null;

        this.stopAtFirstNonClosableGoal = stopAtFirstNonCloseableGoal;

        ProofTreeListener treeListener = prepareStrategy(proof, goals, maxSteps, timeout);
        ApplyStrategyInfo<Goal> result;
        try (var ignored =
            proof.setRuleAppIndexMode(proof.getActiveStrategy().getRuleAppIndexMode())) {
            result = executeStrategy(treeListener);
        } catch (Exception e) { // should never be reached
            throw new RuntimeException(e);
        }
        finishStrategy(result);
        return result;
    }


    private ProofTreeListener prepareStrategy(Proof proof, ImmutableList<Goal> goals, int maxSteps,
            long timeout) {
        ProofTreeListener treeListener = new ProofTreeAdapter() {
            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {
                Iterable<Goal> newGoals = e.getGoals();
                // Check for a closed goal ...
                if (!newGoals.iterator().hasNext()) {
                    // No new goals have been generated ...
                    closedGoals++;
                }
            }
        };
        proof.addProofTreeListener(treeListener);
        init(proof, goals, maxSteps, timeout);

        return treeListener;
    }

    private ApplyStrategyInfo<Goal> executeStrategy(ProofTreeListener treeListener) {
        assert proof() != null;

        ProofListener pl = new ProofListener();
        proof().addRuleAppListener(pl);
        ApplyStrategyInfo<Goal> result;
        try {
            result = doWork(goalChooser, stopCondition);
        } finally {
            proof().removeProofTreeListener(treeListener);
            proof().removeRuleAppListener(pl);
            setAutoModeActive(false);
        }
        return result;
    }

    private void finishStrategy(ApplyStrategyInfo<Goal> result) {
        assert result != null; // CS
        proof().addAutoModeTime(result.getTime());
        fireTaskFinished(new DefaultTaskFinishedInfo(this, result, proof(), result.getTime(),
            result.getNumberOfAppliedRuleApps(), result.getNumberOfClosedGoals()));
    }

    /**
     * Returns the {@link GoalChooser} to use for the given {@link Proof}. This is the custom one
     * defined in the proof's {@link StrategySettings} or the default one of this
     * {@link ApplyStrategy#defaultGoalChooser} otherwise.
     *
     * @param proof The {@link Proof} for which an {@link GoalChooser} is required.
     * @return The {@link GoalChooser} to use.
     */
    private GoalChooser<Goal> getGoalChooserForProof(Proof proof) {
        GoalChooser<Goal> chooser = null;
        if (proof != null) {
            chooser = proof.getSettings().getStrategySettings().getCustomApplyStrategyGoalChooser();
        }
        return chooser != null ? chooser : defaultGoalChooser;
    }

    @Override
    protected final @Nullable RuleApp updateBuiltInRuleIndex(Goal goal, @Nullable RuleApp app) {
        // Hack: built in rules may become applicable without BuiltInRuleAppIndex noticing---->
        if (app == null) {
            goal.ruleAppIndex().scanBuiltInRules(goal);
            app = goal.getRuleAppManager().next();
        }
        // <-------
        return app;
    }

    private class ProofListener implements RuleAppListener {

        /** invoked when a rule has been applied */
        @Override
        public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive()) {
                return;
            }
            RuleAppInfo rai = e.getRuleAppInfo();
            if (rai == null) {
                return;
            }

            final GoalChooser<Goal> goalChooser =
                getGoalChooserForProof(rai.getOriginalNode().proof());
            synchronized (goalChooser) {
                // reverse just to keep old order
                goalChooser.updateGoalList(rai.getOriginalNode(), e.getNewGoals().reverse());
            }
        }
    }

    private boolean isAutoModeActive() {
        return autoModeActive;
    }

    private void setAutoModeActive(boolean autoModeActive) {
        this.autoModeActive = autoModeActive;
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#clear()
     */
    @Override
    public void clear() {
        final GoalChooser<Goal> goalChooser = getGoalChooserForProof(proof());
        proof = null;
        if (goalChooser != null) {
            goalChooser.init(null, ImmutableList.nil());
        }
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#hasBeenInterrupted()
     */
    @Override
    public boolean hasBeenInterrupted() {
        return cancelled;
    }
}
