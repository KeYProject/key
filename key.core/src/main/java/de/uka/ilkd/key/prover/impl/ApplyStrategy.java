/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
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
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

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
public class ApplyStrategy extends DefaultProver<Proof, Goal> {
    public static final Logger LOGGER = LoggerFactory.getLogger(ApplyStrategy.class);

    public static final AtomicLong PERF_GOAL_APPLY = new AtomicLong();

    /**
     * The default {@link GoalChooser} to choose goals to which rules are applied if the
     * {@link StrategySettings} of the proof provides no customized one.
     */
    private final GoalChooser<Proof, Goal> defaultGoalChooser;

    /** interrupted by the user? */
    private boolean autoModeActive = false;

    // Please create this object beforehand and re-use it.
    // Otherwise, the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(GoalChooser<Proof, Goal> defaultGoalChooser) {
        this.defaultGoalChooser = defaultGoalChooser;
    }

    private void init(Proof newProof, ImmutableList<Goal> goals, int maxSteps, long timeout) {
        this.proof = newProof;
        maxApplications = maxSteps;
        this.timeout = timeout;
        countApplied = 0;
        closedGoals = 0;
        cancelled = false;
        stopCondition = proof.getSettings().getStrategySettings().getApplyStrategyStopCondition();
        assert stopCondition != null;
        goalChooser = getGoalChooserForProof(proof);
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
    public synchronized ApplyStrategyInfo<Proof, Goal> start(Proof proof, Goal goal) {
        return start(proof, ImmutableSLList.<Goal>nil().prepend(goal));
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * org.key_project.util.collection.ImmutableList)
     */
    @Override
    public synchronized ApplyStrategyInfo<Proof, Goal> start(Proof proof,
            ImmutableList<Goal> goals) {
        ProofSettings settings = proof.getSettings();
        StrategySettings stratSet = settings.getStrategySettings();
        return start(proof, goals, stratSet);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * org.key_project.util.collection.ImmutableList, de.uka.ilkd.key.settings.StrategySettings)
     */
    @Override
    public synchronized ApplyStrategyInfo<Proof, Goal> start(Proof proof, ImmutableList<Goal> goals,
            Object strategySettings) {

        final StrategySettings stratSet = (StrategySettings) strategySettings;
        int maxSteps = stratSet.getMaxSteps();
        long timeout = stratSet.getTimeout();

        boolean stopAtFirstNonCloseableGoal = proof.getSettings().getStrategySettings()
                .getActiveStrategyProperties().getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
        return start(proof, goals, maxSteps, timeout, stopAtFirstNonCloseableGoal);
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * org.key_project.util.collection.ImmutableList, int, long, boolean)
     */
    @Override
    public synchronized ApplyStrategyInfo<Proof, Goal> start(Proof proof, ImmutableList<Goal> goals,
            int maxSteps, long timeout, boolean stopAtFirstNonCloseableGoal) {
        assert proof != null;

        this.stopAtFirstNonClosableGoal = stopAtFirstNonCloseableGoal;

        ProofTreeListener treeListener = prepareStrategy(proof, goals, maxSteps, timeout);
        ApplyStrategyInfo<Proof, Goal> result = executeStrategy(treeListener);
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

    private ApplyStrategyInfo<Proof, Goal> executeStrategy(ProofTreeListener treeListener) {
        assert proof != null;

        ProofListener pl = new ProofListener();
        proof.addRuleAppListener(pl);
        ApplyStrategyInfo<Proof, Goal> result;
        try {
            result = doWork(goalChooser, stopCondition);
        } finally {
            proof.removeProofTreeListener(treeListener);
            proof.removeRuleAppListener(pl);
            setAutoModeActive(false);
        }
        return result;
    }

    private void finishStrategy(ApplyStrategyInfo<Proof, Goal> result) {
        assert result != null; // CS
        proof.addAutoModeTime(result.getTime());
        fireTaskFinished(new DefaultTaskFinishedInfo(this, result, proof, result.getTime(),
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
    private GoalChooser<Proof, Goal> getGoalChooserForProof(Proof proof) {
        GoalChooser<Proof, Goal> chooser = null;
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

            final GoalChooser<Proof, Goal> goalChooser =
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
        final GoalChooser<Proof, Goal> goalChooser = getGoalChooserForProof(proof);
        proof = null;
        if (goalChooser != null) {
            goalChooser.init(null, ImmutableSLList.nil());
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

//
/// **
// * applies rules that are chosen by the active strategy
// *
// * @return information whether the rule application was successful or not
// */
// protected synchronized SingleRuleApplicationInfo applyAutomaticRule(
// final GoalChooser<Proof, Goal> goalChooser,
// final StopCondition<Goal> stopCondition, boolean stopAtFirstNonClosableGoal) {
// // Look for the strategy ...
// RuleApp app = null;
// Goal g;
// while ((g = goalChooser.getNextGoal()) != null) {
// if (!stopCondition.isGoalAllowed(g, maxApplications, timeout, time, countApplied)) {
// return new SingleRuleApplicationInfo(stopCondition.getGoalNotAllowedMessage(
// g, maxApplications, timeout, time, countApplied), g, null);
// }
// app = g.getRuleAppManager().next();
// // Hack: built in rules may become applicable without BuiltInRuleAppIndex noticing---->
// if (app == null) {
// g.ruleAppIndex().scanBuiltInRules(g);
// app = g.getRuleAppManager().next();
// }
// // <-------
//
// if (app == null) {
// if (stopAtFirstNonClosableGoal) {
// return new SingleRuleApplicationInfo("Could not close goal.", g, app);
// }
// goalChooser.removeGoal(g);
// } else {
// break;
// }
// }
// if (app == null) {
// return new SingleRuleApplicationInfo(
// "No more rules automatically applicable to any goal.", g, app);
// } else {
// var time = System.nanoTime();
// try {
// g.apply(app);
// } finally {
// PERF_GOAL_APPLY.getAndAdd(System.nanoTime() - time);
// }
// return new SingleRuleApplicationInfo(g, app);
// }
// }
//
/// **
// * applies rules until this is no longer possible or the thread is interrupted.
// */
// private synchronized ApplyStrategyInfo<Proof,Goal> doWork(final GoalChooser<Proof, Goal>
// goalChooser,
// final StopCondition<Goal> stopCondition) {
// time = System.currentTimeMillis();
// SingleRuleApplicationInfo srInfo = null;
//
// var perfScope = new PerfScope();
// long applyAutomatic = 0;
// try {
// LOGGER.trace("Strategy started.");
// boolean shouldStop = stopCondition.shouldStop(maxApplications, timeout, time,
// countApplied, srInfo);
//
// while (!shouldStop) {
// var applyAutomaticTime = System.nanoTime();
// try {
// srInfo =
// applyAutomaticRule(goalChooser, stopCondition, stopAtFirstNonClosableGoal);
// } finally {
// applyAutomatic += System.nanoTime() - applyAutomaticTime;
// }
// if (!srInfo.isSuccess()) {
// return new ApplyStrategyInfo<>(srInfo.message(), proof, null, srInfo.getGoal(),
// System.currentTimeMillis() - time, countApplied, closedGoals);
// }
// countApplied++;
// fireTaskProgress();
// if (Thread.interrupted()) {
// throw new InterruptedException();
// }
// shouldStop = stopCondition.shouldStop(maxApplications, timeout, time, countApplied, srInfo);
// }
// if (shouldStop) {
// return new ApplyStrategyInfo<>(
// stopCondition.getStopMessage(maxApplications, timeout, time,
// countApplied, srInfo),
// proof, null, null, System.currentTimeMillis() - time, countApplied,
// closedGoals);
// }
// } catch (InterruptedException e) {
// cancelled = true;
// return new ApplyStrategyInfo<>("Interrupted.", proof, null, goalChooser.getNextGoal(),
// System.currentTimeMillis() - time, countApplied, closedGoals);
// } catch (Throwable t) { // treated later in finished()
// LOGGER.warn("doWork exception", t);
// return new ApplyStrategyInfo<>("Error.", proof, t, null,
// System.currentTimeMillis() - time, countApplied, closedGoals);
// } finally {
// time = (System.currentTimeMillis() - time);
// LOGGER.trace("Strategy stopped, applied {} steps in {}ms", countApplied, time);
//
// LOGGER.trace("applyAutomaticRule: " + PerfScope.formatTime(applyAutomatic));
// perfScope.report();
// }
// assert srInfo != null;
// return new ApplyStrategyInfo<>(srInfo.message(), proof, null, srInfo.getGoal(), time,
// countApplied, closedGoals);
// }
