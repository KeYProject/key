/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.prover;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.impl.ApplyStrategy;
import de.uka.ilkd.key.prover.impl.SingleRuleApplicationInfo;
import de.uka.ilkd.key.settings.StrategySettings;

/**
 * <p>
 * Implementation of this interface are used in {@link ApplyStrategy} to determine if the strategy
 * should stop or continue.
 * </p>
 * <p>
 * The first check is done before a rule is applied on a {@link Goal} via
 * {@link #isGoalAllowed(ApplyStrategy, int, long, Proof, GoalChooser, long, int, Goal)}. If this
 * method returns {@code false} the strategy stops and the reason shown to the user is computed via
 * {@link #getGoalNotAllowedMessage(ApplyStrategy, int, long, Proof, GoalChooser, long, int, Goal)}.
 * </p>
 * <p>
 * The second check is after a rule was applied via
 * {@link #shouldStop(ApplyStrategy, int, long, Proof, GoalChooser, long, int, SingleRuleApplicationInfo)}.
 * If this method returns {@code true} the strategy stops and the reason shown to the user is
 * computed via
 * {@link #getStopMessage(ApplyStrategy, int, long, Proof, GoalChooser, long, int, SingleRuleApplicationInfo)}.
 * </p>
 * <p>
 * <b>Attention: </b> It is possible that an {@link StopCondition} has to check one {@link Goal}
 * with the same node multiple times. It is required that the called check method always returns the
 * same result for the same {@link Node} of a {@link Goal}.
 * </p>
 *
 * @author Martin Hentschel
 */
public interface StopCondition {
    /**
     * Returns the maximal amount of work needed to complete the task, used to display a progress
     * bar. Pass {@code 0} to indicate unknown size.
     *
     * @param maxApplications The defined maximal number of rules to apply. Can be different to
     *        {@link StrategySettings#getMaxSteps()} in side proofs.
     * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to
     *        {@link StrategySettings#getTimeout()} in side proofs.
     * @param proof The current {@link Proof}.
     * @return The maximal amount of work or {@code 0} if it is unknown.
     */
    int getMaximalWork(int maxApplications, long timeout, Proof proof);

    /**
     * Checks if it is allowed to apply the next rule on the selected {@link Goal} chosen by the
     * {@link GoalChooser} before it is applied. If it is not allowed the apply strategy will stop.
     *
     * @param maxApplications The defined maximal number of rules to apply. Can be different to
     *        {@link StrategySettings#getMaxSteps()} in side proofs.
     * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to
     *        {@link StrategySettings#getTimeout()} in side proofs.
     * @param proof The current {@link Proof}.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @param goal The current {@link Goal} on which the next rule will be applied.
     * @return {@code true} rule application is allowed, {@code false} rule application is not
     *         allowed so stop apply strategy
     */
    boolean isGoalAllowed(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, Goal goal);

    /**
     * Returns the reason why the previous check via
     * {@link #isGoalAllowed(ApplyStrategy, int, long, Proof, GoalChooser, long, int, Goal)} has
     * stopped the apply strategy.
     *
     * @param maxApplications The defined maximal number of rules to apply. Can be different to
     *        {@link StrategySettings#getMaxSteps()} in side proofs.
     * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to
     *        {@link StrategySettings#getTimeout()} in side proofs.
     * @param proof The current {@link Proof}.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @param goal The current {@link Goal} on which the next rule will be applied.
     * @return
     */
    String getGoalNotAllowedMessage(int maxApplications, long timeout, Proof proof,
            long startTime, int countApplied, Goal goal);

    /**
     * Checks after each applied rule if more rules should be applied or if the strategy should
     * stop.
     *
     * @param maxApplications The defined maximal number of rules to apply. Can be different to
     *        {@link StrategySettings#getMaxSteps()} in side proofs.
     * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to
     *        {@link StrategySettings#getTimeout()} in side proofs.
     * @param proof The current {@link Proof}.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @param singleRuleApplicationInfo An optional {@link SingleRuleApplicationInfo}.
     * @return {@code true} stop strategy, {@code false} continue strategy and apply next rule.
     */
    boolean shouldStop(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo);

    /**
     * Returns a human readable message which explains why the previous
     * {@link #shouldStop(ApplyStrategy, Proof, GoalChooser, long, int, SingleRuleApplicationInfo)}
     * has stopped the strategy.
     *
     * @param maxApplications The defined maximal number of rules to apply. Can be different to
     *        {@link StrategySettings#getMaxSteps()} in side proofs.
     * @param timeout The defined timeout in ms or {@code -1} if disabled. Can be different to
     *        {@link StrategySettings#getTimeout()} in side proofs.
     * @param proof The current {@link Proof}.
     * @param startTime The timestamp when the apply strategy has started, computed via
     *        {@link System#currentTimeMillis()}
     * @param countApplied The number of already applied rules.
     * @param singleRuleApplicationInfo An optional {@link SingleRuleApplicationInfo}.
     * @return The human readable message which explains the stop reason.
     */
    String getStopMessage(int maxApplications, long timeout, Proof proof, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo);
}
