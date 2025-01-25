/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine.impl;

import java.util.concurrent.atomic.AtomicLong;

import org.key_project.prover.engine.AbstractProverCore;
import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.SingleRuleApplicationInfo;
import org.key_project.prover.engine.StopCondition;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.prover.rules.RuleApp;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * A default implementation of prover that can be easily reused via subclassing.
 *
 * @param <Proof> the type of {@link ProofObject} which the prover constructs
 * @param <Goal> the type of goals {@link ProofGoal} manipulated by this prover
 */
public abstract class DefaultProver<Proof extends ProofObject<@NonNull Goal>, Goal extends ProofGoal<@NonNull Goal>>
        extends AbstractProverCore<Proof, Goal> {

    private final static Logger LOGGER = LoggerFactory.getLogger(DefaultProver.class);
    public static final AtomicLong PERF_GOAL_APPLY = new AtomicLong();

    /**
     * the proof that is worked with
     */
    protected Proof proof;
    /**
     * the maximum of allowed rule applications
     */
    protected int maxApplications;

    /** the start time of the most recent prover invocation */
    protected long time;

    /** time in ms after which rule application shall be aborted, -1 disables timeout */
    protected long timeout = -1;

    /** true if the prover should stop as soon as a non-closable goal is detected */
    protected boolean stopAtFirstNonClosableGoal;

    /** the number of (so far) closed goal by the current running strategy */
    protected int closedGoals;

    /** indicates whether the prover has been interrupted and should stop */
    protected boolean cancelled;

    /** a configurable condition indicating that the prover has to stop, */
    protected StopCondition<Goal> stopCondition;

    /** the goal choose picks the next goal to work on */
    protected GoalChooser<Proof, Goal> goalChooser;

    /**
     * This is currently a hook method for the JavaDL prover as according to a
     * comment the built-in-rule index is not updated when rules are applied.
     * <p>
     * Ultimately, this has to be fixed in the listener structure of JavaDL.
     * But for the moment we move it up. Other implementations should implement
     * this method as an empty method.
     * </p>
     *
     * @param goal the {@link Goal} on which the prover currently works
     * @param app the {@link RuleApp} to be applied next (if null, the built-in-rule
     *        index is updated and queried whether a built-in rule is applicable)
     * @return the next rule app to be applied or {@code null} if none
     */
    protected abstract @Nullable RuleApp updateBuiltInRuleIndex(Goal goal, @Nullable RuleApp app);

    /**
     * applies rules until this is no longer possible or the thread is interrupted.
     */
    protected final synchronized ApplyStrategyInfo<Proof, Goal> doWork(
            final GoalChooser<Proof, Goal> goalChooser,
            final StopCondition<Goal> stopCondition) {
        long time = System.currentTimeMillis();
        SingleRuleApplicationInfo srInfo = null;

        long applyAutomatic = 0;
        try {
            LOGGER.trace("Strategy started.");
            boolean shouldStop = stopCondition.shouldStop(maxApplications, timeout, time,
                countApplied, srInfo);
            while (!shouldStop) {
                var applyAutomaticTime = System.nanoTime();
                try {
                    srInfo = applyAutomaticRule(goalChooser, stopCondition,
                        time, stopAtFirstNonClosableGoal);
                } finally {
                    applyAutomatic += System.nanoTime() - applyAutomaticTime;
                }
                if (!srInfo.isSuccess()) {
                    return new ApplyStrategyInfo<>(srInfo.message(), proof, null, srInfo.getGoal(),
                        System.currentTimeMillis() - time, countApplied, closedGoals);
                }
                countApplied++;
                fireTaskProgress();
                if (Thread.interrupted()) {
                    throw new InterruptedException();
                }
                shouldStop =
                    stopCondition.shouldStop(maxApplications, timeout, time, countApplied, srInfo);
            }
            return new ApplyStrategyInfo<>(
                stopCondition.getStopMessage(maxApplications, timeout, time,
                    countApplied, srInfo),
                proof, null, null, System.currentTimeMillis() - time, countApplied,
                closedGoals);
        } catch (InterruptedException e) {
            cancelled = true;
            return new ApplyStrategyInfo<>("Interrupted.", proof, null, goalChooser.getNextGoal(),
                System.currentTimeMillis() - time, countApplied, closedGoals);
        } catch (Throwable t) { // treated later in finished()
            LOGGER.warn("doWork exception", t);
            return new ApplyStrategyInfo<>("Error.", proof, t, null,
                System.currentTimeMillis() - time, countApplied, closedGoals);
        } finally {
            time = (System.currentTimeMillis() - time);
            LOGGER.trace("Strategy stopped, applied {} steps in {}ms", countApplied, time);
            LOGGER.trace("applyAutomaticRule: " + applyAutomatic);
        }
    }

    /**
     * applies rules that are chosen by the active strategy
     *
     * @return information whether the rule application was successful or not
     */
    protected final synchronized SingleRuleApplicationInfo applyAutomaticRule(
            final GoalChooser<Proof, Goal> goalChooser,
            final StopCondition<Goal> stopCondition,
            long startTime, boolean stopAtFirstNonClosableGoal) {
        // Look for the strategy ...
        RuleApp app = null;
        Goal g;
        while ((g = goalChooser.getNextGoal()) != null) {
            if (!stopCondition.isGoalAllowed(g, maxApplications, timeout, startTime,
                countApplied)) {
                return new SingleRuleApplicationInfo(stopCondition.getGoalNotAllowedMessage(
                    g, maxApplications, timeout, startTime, countApplied), g, null);
            }

            app = g.getRuleAppManager().next();

            app = updateBuiltInRuleIndex(g, app);

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
            try {
                g.apply(app);
            } finally {
                PERF_GOAL_APPLY.getAndAdd(System.nanoTime() - time);
            }
            return new SingleRuleApplicationInfo(g, app);
        }
    }
}
