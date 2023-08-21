/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover.impl;


import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;
import de.uka.ilkd.key.prover.GoalChooser;
import de.uka.ilkd.key.prover.StopCondition;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.settings.StrategySettings;
import de.uka.ilkd.key.strategy.StrategyProperties;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Applies rules in an automated fashion. The caller should ensure that the strategy runs in its own
 * thread
 * <a href="http://java.sun.com/products/jfc/tsc/articles/threads/threads2.html">Uses code by Hans
 * Muller
 * and Kathy Walrath</a>
 *
 * @author Richard Bubel
 */
public class ApplyStrategy extends AbstractProverCore {
    public static final Logger LOGGER = LoggerFactory.getLogger(ApplyStrategy.class);

    public static final AtomicLong PERF_GOAL_APPLY = new AtomicLong();

    /**
     * the proof that is worked with
     */
    private Proof proof;
    /** the maximum of allowed rule applications */
    private int maxApplications;

    /**
     * The default {@link GoalChooser} to choose goals to which rules are applied if the
     * {@link StrategySettings} of the proof provides no customized one.
     */
    private final GoalChooser defaultGoalChooser;

    private long time;

    /** interrupted by the user? */
    private boolean autoModeActive = false;

    /** time in ms after which rule application shall be aborted, -1 disables timeout */
    private long timeout = -1;
    /** true if the prover should stop as soon as a non closable goal is detected */
    private boolean stopAtFirstNonClosableGoal;
    /** the number of (so far) closed goal by the current running strategy */
    private int closedGoals;
    /** indicates whether the prover has been interrupted and should stop */
    private boolean cancelled;
    /** a configurable condition indicating that the prover has to stop, */
    private StopCondition stopCondition;
    /** the goal choose picks the next goal to work on */
    private GoalChooser goalChooser;

    // Please create this object beforehand and re-use it.
    // Otherwise the addition/removal of the InteractiveProofListener
    // can cause a ConcurrentModificationException during ongoing operation
    public ApplyStrategy(GoalChooser defaultGoalChooser) {
        this.defaultGoalChooser = defaultGoalChooser;
    }

    /**
     * applies rules that are chosen by the active strategy
     *
     * @return true iff a rule has been applied, false otherwise
     */
    private synchronized SingleRuleApplicationInfo applyAutomaticRule(final GoalChooser goalChooser,
            final StopCondition stopCondition, boolean stopAtFirstNonClosableGoal) {
        // Look for the strategy ...
        RuleApp app = null;
        Goal g;
        while ((g = goalChooser.getNextGoal()) != null) {
            if (!stopCondition.isGoalAllowed(maxApplications, timeout, proof, time, countApplied,
                g)) {
                return new SingleRuleApplicationInfo(stopCondition.getGoalNotAllowedMessage(
                    maxApplications, timeout, proof, time, countApplied, g), g, null);
            }
            app = g.getRuleAppManager().next();
            // Hack: built in rules may become applicable without BuiltInRuleAppIndex noticing---->
            if (app == null) {
                g.ruleAppIndex().scanBuiltInRules(g);
                app = g.getRuleAppManager().next();
            }
            // <-------

            if (app == null) {
                if (stopAtFirstNonClosableGoal) {
                    return new SingleRuleApplicationInfo("Could not close goal.", g, app);
                }
                goalChooser.removeGoal(g);
            } else {
                break;
            }
        }
        if (app == null) {
            return new SingleRuleApplicationInfo(
                "No more rules automatically applicable to any goal.", g, app);
        } else {
            assert g != null;
            var time = System.nanoTime();
            try {
                g.apply(app);
            } finally {
                PERF_GOAL_APPLY.getAndAdd(System.nanoTime() - time);
            }
            return new SingleRuleApplicationInfo(g, app);
        }
    }

    /**
     * applies rules until this is no longer possible or the thread is interrupted.
     */
    private synchronized ApplyStrategyInfo doWork(final GoalChooser goalChooser,
            final StopCondition stopCondition) {
        time = System.currentTimeMillis();
        SingleRuleApplicationInfo srInfo = null;

        var perfScope = new PerfScope();
        long applyAutomatic = 0;
        try {
            LOGGER.trace("Strategy started.");
            boolean shouldStop = stopCondition.shouldStop(maxApplications, timeout, proof, time,
                countApplied, srInfo);

            while (!shouldStop) {
                var applyAutomaticTime = System.nanoTime();
                try {
                    srInfo =
                        applyAutomaticRule(goalChooser, stopCondition, stopAtFirstNonClosableGoal);
                } finally {
                    applyAutomatic += System.nanoTime() - applyAutomaticTime;
                }
                if (!srInfo.isSuccess()) {
                    return new ApplyStrategyInfo(srInfo.message(), proof, null, srInfo.getGoal(),
                        System.currentTimeMillis() - time, countApplied, closedGoals);
                }
                countApplied++;
                fireTaskProgress();
                if (Thread.interrupted()) {
                    throw new InterruptedException();
                }
                shouldStop = stopCondition.shouldStop(maxApplications, timeout, proof, time,
                    countApplied, srInfo);
            }
            if (shouldStop) {
                return new ApplyStrategyInfo(
                    stopCondition.getStopMessage(maxApplications, timeout, proof, time,
                        countApplied, srInfo),
                    proof, null, null, System.currentTimeMillis() - time, countApplied,
                    closedGoals);
            }
        } catch (InterruptedException e) {
            cancelled = true;
            return new ApplyStrategyInfo("Interrupted.", proof, null, goalChooser.getNextGoal(),
                System.currentTimeMillis() - time, countApplied, closedGoals);
        } catch (Throwable t) { // treated later in finished()
            LOGGER.warn("doWork exception", t);
            return new ApplyStrategyInfo("Error.", proof, t, null,
                System.currentTimeMillis() - time, countApplied, closedGoals);
        } finally {
            time = (System.currentTimeMillis() - time);
            LOGGER.trace("Strategy stopped, applied {} steps in {}ms", countApplied, time);

            LOGGER.trace("applyAutomaticRule: " + PerfScope.formatTime(applyAutomatic));
            perfScope.report();
        }
        assert srInfo != null;
        return new ApplyStrategyInfo(srInfo.message(), proof, null, srInfo.getGoal(), time,
            countApplied, closedGoals);
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
        fireTaskStarted(stopCondition.getMaximalWork(maxSteps, timeout, newProof));
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * de.uka.ilkd.key.proof.Goal)
     */
    @Override
    public synchronized ApplyStrategyInfo start(Proof proof, Goal goal) {
        return start(proof, ImmutableSLList.<Goal>nil().prepend(goal));
    }

    /*
     * (non-Javadoc)
     *
     * @see de.uka.ilkd.key.prover.ProverCore#start(de.uka.ilkd.key.proof.Proof,
     * org.key_project.util.collection.ImmutableList)
     */
    @Override
    public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals) {
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
    public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals,
            StrategySettings stratSet) {

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
    public synchronized ApplyStrategyInfo start(Proof proof, ImmutableList<Goal> goals,
            int maxSteps, long timeout, boolean stopAtFirstNonCloseableGoal) {
        assert proof != null;

        this.stopAtFirstNonClosableGoal = stopAtFirstNonCloseableGoal;

        ProofTreeListener treeListener = prepareStrategy(proof, goals, maxSteps, timeout);
        ApplyStrategyInfo result = executeStrategy(treeListener);
        finishStrategy(result);
        return result;
    }


    private ProofTreeListener prepareStrategy(Proof proof, ImmutableList<Goal> goals, int maxSteps,
            long timeout) {
        ProofTreeListener treeListener = new ProofTreeAdapter() {
            @Override
            public void proofGoalsAdded(ProofTreeEvent e) {
                ImmutableList<Goal> newGoals = e.getGoals();
                // Check for a closed goal ...
                if (newGoals.size() == 0) {
                    // No new goals have been generated ...
                    closedGoals++;
                }
            }
        };
        proof.addProofTreeListener(treeListener);
        init(proof, goals, maxSteps, timeout);

        return treeListener;
    }

    private ApplyStrategyInfo executeStrategy(ProofTreeListener treeListener) {
        assert proof != null;

        ProofListener pl = new ProofListener();
        proof.addRuleAppListener(pl);
        ApplyStrategyInfo result = null;
        try {
            result = doWork(goalChooser, stopCondition);
        } finally {
            proof.removeProofTreeListener(treeListener);
            proof.removeRuleAppListener(pl);
            setAutoModeActive(false);
        }
        return result;
    }

    private void finishStrategy(ApplyStrategyInfo result) {
        assert result != null; // CS
        proof.addAutoModeTime(result.getTime());
        fireTaskFinished(new DefaultTaskFinishedInfo(this, result, proof, result.getTime(),
            result.getAppliedRuleApps(), result.getClosedGoals()));
    }

    /**
     * Returns the {@link GoalChooser} to use for the given {@link Proof}. This is the custom one
     * defined in the proof's {@link StrategySettings} or the default one of this
     * {@link ApplyStrategy#defaultGoalChooser} otherwise.
     *
     * @param proof The {@link Proof} for which an {@link GoalChooser} is required.
     * @return The {@link GoalChooser} to use.
     */
    private GoalChooser getGoalChooserForProof(Proof proof) {
        GoalChooser chooser = null;
        if (proof != null) {
            chooser = proof.getSettings().getStrategySettings().getCustomApplyStrategyGoalChooser();
        }
        return chooser != null ? chooser : defaultGoalChooser;
    }

    private class ProofListener implements RuleAppListener {

        /** invoked when a rule has been applied */
        public void ruleApplied(ProofEvent e) {
            if (!isAutoModeActive()) {
                return;
            }
            RuleAppInfo rai = e.getRuleAppInfo();
            if (rai == null) {
                return;
            }

            final GoalChooser goalChooser = getGoalChooserForProof(rai.getOriginalNode().proof());
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
        final GoalChooser goalChooser = getGoalChooserForProof(proof);
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
