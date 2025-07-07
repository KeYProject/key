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

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/// A default implementation of a prover that provides reusable functionality
/// for constructing and manipulating proofs by applying rules to goals.
///
/// This class can be subclassed to define custom provers with specific strategies
/// and behaviors for proof construction.
///
///
/// @param <Proof> the type of [ProofObject] that the prover constructs
/// @param <Goal> the type of [ProofGoal] instances manipulated by this prover
public abstract class DefaultProver<Proof extends ProofObject<Goal>, Goal extends @Nullable ProofGoal<Goal>>
        extends AbstractProverCore<Proof, Goal> {

    /// Logger for tracing and debugging the prover's execution.
    private final static Logger LOGGER = LoggerFactory.getLogger(DefaultProver.class);

    /// Counter for tracking performance metrics related to goal application.
    public static final AtomicLong PERF_GOAL_APPLY = new AtomicLong();

    /// The proof currently being constructed or manipulated by this prover.
    protected @MonotonicNonNull Proof proof;

    /// The maximum number of rule applications allowed during the proof process.
    protected int maxApplications;

    /// The start time of the most recent prover invocation, measured in milliseconds.
    protected long time;

    /// The timeout duration, in milliseconds, after which rule application will be aborted.
    /// A value of `-1` disables the timeout.
    protected long timeout = -1;

    /// Indicates whether the prover should stop as soon as a non-closable goal is detected.
    protected boolean stopAtFirstNonClosableGoal;

    /// The number of goals closed during the current proof process.
    protected int closedGoals;

    /// Indicates whether the prover has been interrupted and should stop.
    protected boolean cancelled;

    /// A condition that determines whether the prover should stop its execution.
    protected @Nullable StopCondition<Goal> stopCondition;

    /// A strategy component that selects the next goal to be processed.
    protected @Nullable GoalChooser<Proof, Goal> goalChooser;

    /// This is currently a hook method for the JavaDL prover as according to a
    /// comment the built-in-rule index is not updated when rules are applied.
    ///
    /// Ultimately, this has to be fixed in the listener structure of JavaDL.
    /// But for the moment we move it up. Other implementations should implement
    /// this method as an empty method.
    ///
    ///
    /// @param goal the [Goal] currently being processed
    /// @param app the [RuleApp] to be applied next (if null, the built-in-rule
    /// index is updated and queried whether a built-in rule is applicable)
    /// @return the next [RuleApp] to apply, or `null` if no rule is applicable
    protected abstract @Nullable RuleApp updateBuiltInRuleIndex(Goal goal, @Nullable RuleApp app);

    /// Executes the proof strategy by applying rules to goals until no further rules
    /// can be applied, a stop condition is met, or the thread is interrupted.
    ///
    /// @param goalChooser the [GoalChooser] that determines the next goal to process
    /// @param stopCondition the [StopCondition] that dictates when the prover should stop
    /// @return an [ApplyStrategyInfo] instance containing details about the proof process
    protected final synchronized ApplyStrategyInfo<Proof, Goal> doWork(
            final GoalChooser<Proof, Goal> goalChooser,
            final StopCondition<Goal> stopCondition) {
        assert proof != null : "@AssumeAssertion(nullness): proof cannot be null";
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
                    return new ApplyStrategyInfo<>(srInfo.message(), proof,
                        null, srInfo.getGoal(),
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
            return new ApplyStrategyInfo<Proof, Goal>("Interrupted.", proof, null,
                goalChooser.getNextGoal(),
                System.currentTimeMillis() - time, countApplied, closedGoals);
        } catch (Throwable t) { // treated later in finished()
            LOGGER.warn("doWork exception", t);
            return new ApplyStrategyInfo<>("Error.", proof, t, null,
                System.currentTimeMillis() - time, countApplied, closedGoals);
        } finally {
            time = (System.currentTimeMillis() - time);
            LOGGER.trace("Strategy stopped, applied {} steps in {}ms", countApplied, time);
            LOGGER.trace("applyAutomaticRule: {} ", applyAutomatic);
        }
    }

    /// Applies rules to goals using the active strategy until a stopping condition is met.
    ///
    /// @param goalChooser the [GoalChooser] for selecting the next goal
    /// @param stopCondition the [StopCondition] to evaluate during processing
    /// @param startTime the start time of the current proof process, in milliseconds
    /// @param stopAtFirstNonClosableGoal whether to stop if a non-closable goal is detected
    /// @return a [SingleRuleApplicationInfo] instance containing the result of the rule
    /// application
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
                @SuppressWarnings({ "nullness", "unused" })
                final var result = g.apply(app);
            } finally {
                PERF_GOAL_APPLY.getAndAdd(System.nanoTime() - time);
            }
            return new SingleRuleApplicationInfo(g, app);
        }
    }
}
