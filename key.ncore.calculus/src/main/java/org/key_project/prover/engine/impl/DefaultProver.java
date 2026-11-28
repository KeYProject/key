/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.engine.impl;


import org.key_project.prover.engine.AbstractProverCore;
import org.key_project.prover.engine.GoalChooser;
import org.key_project.prover.engine.SingleRuleApplicationInfo;
import org.key_project.prover.engine.StopCondition;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.prover.rules.RuleApp;
import org.key_project.util.collection.ImmutableList;

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
/// @param <Goal> the type of [ProofGoal] instances manipulated by this prover
public abstract class DefaultProver<Goal extends ProofGoal<Goal>>
        extends AbstractProverCore<Goal> {

    /// Logger for tracing and debugging the prover's execution.
    private final static Logger LOGGER = LoggerFactory.getLogger(DefaultProver.class);

    /// The proof currently being constructed or manipulated by this prover.
    protected @MonotonicNonNull ProofObject<Goal> proof;

    /// The maximum number of rule applications allowed during the proof process.
    protected int maxApplications;

    /// The timeout duration, in milliseconds, after which rule application will be aborted.
    /// A value of `-1` disables the timeout.
    protected long timeout = -1;

    /// Indicates whether the prover should stop as soon as a non-closable goal is detected.
    protected boolean stopAtFirstNonClosableGoal;

    /// Indicates whether the prover has been interrupted and should stop.
    ///
    /// Written and read only by the thread driving the run (the one that called `start`): its
    /// own interrupt handlers set it, and the driver queries it afterwards via
    /// `hasBeenInterrupted()`. Worker threads of a parallel prover must NOT write it -- a worker
    /// interrupt is part of every wind-down (including error stops) and carries no cancellation
    /// information. Volatile as insurance should a cross-thread write slip back in.
    protected volatile boolean cancelled;

    /// A condition that determines whether the prover should stop its execution.
    protected @Nullable StopCondition<Goal> stopCondition;

    /// A strategy component that selects the next goal to be processed.
    protected @Nullable GoalChooser<Goal> goalChooser;

    /// offers the next applicable rule app for this goal or `null` if there is none
    /// @return the applicable rule app or `null`
    @SuppressWarnings("nullness")
    protected @Nullable RuleApp nextRuleApp(Goal goal) {
        return goal.getRuleAppManager().next();
    }

    /// Executes the proof strategy by applying rules to goals until no further rules
    /// can be applied, a stop condition is met, or the thread is interrupted.
    ///
    /// @param goalChooser the [GoalChooser] that determines the next goal to process
    /// @param stopCondition the [StopCondition] that dictates when the prover should stop
    /// @return an [ApplyStrategyInfo] instance containing details about the proof process
    protected final synchronized ApplyStrategyInfo<Goal> doWork(
            final GoalChooser<Goal> goalChooser,
            final StopCondition<Goal> stopCondition) {
        assert proof != null : "@AssumeAssertion(nullness): proof cannot be null";
        long time = System.currentTimeMillis();
        long closedGoalsAtStart = getClosedGoalCount();
        SingleRuleApplicationInfo srInfo = null;

        final int openGoalCountAtStart = proof.getOpenGoalCount();
        long applyAutomatic = 0;
        try {
            LOGGER.trace("Strategy started.");
            boolean shouldStop = stopCondition.shouldStop(maxApplications, timeout, time,
                countApplied, srInfo);
            while (!shouldStop) {
                if (proof.isErroneous()) {
                    // The proof is flagged as erroneous: stop before applying
                    // anything further. The proof refuses new searches but stays saveable.
                    return new ApplyStrategyInfo<>(
                        "Proof search stopped with an internal error: the proof is marked erroneous "
                            +
                            "but can still be saved for later recovery.",
                        proof, null, srInfo == null ? null : srInfo.getGoal(),
                        System.currentTimeMillis() - time, countApplied,
                        getClosedGoalCount() - openGoalCountAtStart);
                }
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
                        System.currentTimeMillis() - time, countApplied,
                        getClosedGoalCount() - openGoalCountAtStart);
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
                getClosedGoalCount() - openGoalCountAtStart);
        } catch (InterruptedException e) {
            cancelled = true;
            return new ApplyStrategyInfo<>("Interrupted.", proof, null,
                goalChooser.getNextGoal(),
                System.currentTimeMillis() - time, countApplied,
                getClosedGoalCount() - openGoalCountAtStart);
        } catch (Throwable t) { // treated later in finished()
            LOGGER.warn("doWork exception", t);
            return new ApplyStrategyInfo<>("Error.", proof, t, null,
                System.currentTimeMillis() - time, countApplied,
                getClosedGoalCount() - openGoalCountAtStart);
        } finally {
            time = (System.currentTimeMillis() - time);
            LOGGER.trace("Strategy stopped, applied {} steps in {}ms", countApplied, time);
            LOGGER.trace("applyAutomaticRule: {} ", applyAutomatic);
        }
    }

    /// return the number of closed goals of the current proof
    protected abstract int getClosedGoalCount();

    /// Applies rules to goals using the active strategy until a stopping condition is met.
    ///
    /// @param goalChooser the [GoalChooser] for selecting the next goal
    /// @param stopCondition the [StopCondition] to evaluate during processing
    /// @param startTime the start time of the current proof process, in milliseconds
    /// @param stopAtFirstNonClosableGoal whether to stop if a non-closable goal is detected
    /// @return a [SingleRuleApplicationInfo] instance containing the result of the rule
    /// application
    protected final synchronized SingleRuleApplicationInfo applyAutomaticRule(
            final GoalChooser<Goal> goalChooser,
            final StopCondition<Goal> stopCondition,
            long startTime, boolean stopAtFirstNonClosableGoal) {
        // Look for the strategy ...
        RuleApp app = null;
        Goal g;
        while ((g = goalChooser.getNextGoal()) != null) {
            if (!stopCondition.isGoalAllowed(g, maxApplications, timeout, startTime,
                countApplied)) {
                final var message = stopCondition.getGoalNotAllowedMessage(
                    g, maxApplications, timeout, startTime, countApplied);

                return new SingleRuleApplicationInfo(message, g, null);
            }

            app = nextRuleApp(g);

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
                "No more rules automatically applicable to any goal.", null, app);
        } else {
            @SuppressWarnings("nullness") // g is not null here as app != null
            final ImmutableList<Goal> premisses = g.apply(app);
            synchronized (goalChooser) {
                goalChooser.updateGoalList(g, premisses.reverse());
            }
            return new SingleRuleApplicationInfo(g, app);
        }
    }
}
