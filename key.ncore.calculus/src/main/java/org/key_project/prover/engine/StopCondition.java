/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;

/**
 * <p>
 * Implementation of this interface can be used by implementations of
 * {@link org.key_project.prover.engine.ProverCore}
 * to determine if the strategy should stop or continue.
 * </p>
 * <p>
 * The first check is done before a rule is applied on a {@link G} via
 * {@link #isGoalAllowed(ProofGoal, int, long, long, int)}. If this
 * method returns {@code false} the strategy stops and the reason shown to the user is computed via
 * {@link #getGoalNotAllowedMessage(ProofGoal, int, long, long, int)}.
 * </p>
 * <p>
 * The second check is after a rule was applied via
 * {@link #shouldStop(int, long, long, int, SingleRuleApplicationInfo)}.
 * If this method returns {@code true} the strategy stops and the reason shown to the user is
 * computed via
 * {@link #getStopMessage(int, long, long, int, SingleRuleApplicationInfo)}.
 * </p>
 * <p>
 * <b>Attention: </b> It is possible that a {@link StopCondition} has to check one {@link ProofGoal}
 * with the same underlying sequent multiple times. It is required that the called check method
 * always returns the
 * same result.
 * </p>
 *
 * @author Martin Hentschel
 */
public interface StopCondition<G extends ProofGoal<G>> {
    /**
     * Returns the maximal amount of work needed to complete the task, used to display a progress
     * bar. Pass {@code 0} to indicate unknown size.
     *
     * @param maxApplications The defined maximal number of rules to apply.
     * @param timeout The defined timeout in ms or {@code -1} if disabled.
     * @return The maximal amount of work or {@code 0} if it is unknown.
     */
    int getMaximalWork(int maxApplications, long timeout);

    /**
     * Checks if it is allowed to apply the next rule on the selected {@link ProofGoal} chosen by
     * the
     * {@link GoalChooser} before it is applied. If it is not allowed the apply strategy will stop.
     *
     * @param goal The current {@link ProofGoal} on which the next rule will be applied.
     * @param maxApplications The defined maximal number of rules to apply.
     * @param timeout The defined timeout in ms or {@code -1} if disabled.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @return {@code true} rule application is allowed, {@code false} rule application is not
     *         allowed so stop apply strategy
     */
    boolean isGoalAllowed(G goal, int maxApplications, long timeout, long startTime,
            int countApplied);

    /**
     * Returns the reason why the previous check via
     * {@link #isGoalAllowed(ProofGoal, int, long, long, int)} has
     * stopped the apply strategy.
     *
     * @param goal The current {@link ProofGoal} on which the next rule will be applied.
     * @param maxApplications The defined maximal number of rules to apply.
     * @param timeout The defined timeout in ms or {@code -1} if disabled.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @return description of the reason why automatic proof search has stopped
     */
    String getGoalNotAllowedMessage(G goal, int maxApplications, long timeout,
            long startTime, int countApplied);

    /**
     * Checks after each applied rule if more rules should be applied or if the strategy should
     * stop.
     *
     * @param maxApplications The defined maximal number of rules to apply.
     * @param timeout The defined timeout in ms or {@code -1} if disabled.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @param singleRuleApplicationInfo An optional {@link SingleRuleApplicationInfo}.
     * @return {@code true} stop strategy, {@code false} continue strategy and apply next rule.
     */
    boolean shouldStop(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo);

    /**
     * Returns a human-readable message which explains why the previous
     * {@link #shouldStop(int, long, long, int, SingleRuleApplicationInfo)}
     * has stopped the strategy.
     *
     * @param maxApplications The defined maximal number of rules to apply.
     * @param timeout The defined timeout in ms or {@code -1} if disabled.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @param singleRuleApplicationInfo An optional {@link SingleRuleApplicationInfo}.
     * @return The human-readable message which explains the stop reason.
     */
    String getStopMessage(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo);
}
