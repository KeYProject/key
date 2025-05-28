/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;

///
/// Implementation of this interface can be used by implementations of
/// [ProverCore]
/// to determine if the strategy should stop or continue.
///
///
/// The first check is done before a rule is applied on a [G] via
/// [#isGoalAllowed(ProofGoal,int,long,long,int)]. If this
/// method returns `false` the strategy stops and the reason shown to the user is computed
/// via [#getGoalNotAllowedMessage(ProofGoal,int,long,long,int)].
///
///
/// The second check is after a rule was applied via
/// [#shouldStop(int,long,long,int,SingleRuleApplicationInfo)].
/// If this method returns `true` the strategy stops and the reason shown to the user is
/// computed via [#getStopMessage(int,long,long,int,SingleRuleApplicationInfo)].
///
///
/// **Attention: ** It is possible that a [StopCondition] has to check one [ProofGoal]
/// with the same underlying sequent multiple times. It is required that the called check method
/// always returns the same result.
///
///
/// @author Martin Hentschel
public interface StopCondition<G extends ProofGoal<G>> {
    /// Returns the maximal amount of work needed to complete the task, used to display a
    /// progress bar. Pass `0` to indicate unknown size.
    ///
    /// @param maxApplications The defined maximal number of rules to apply.
    /// @param timeout The defined timeout in ms or `-1` if disabled.
    /// @return The maximal amount of work or `0` if it is unknown.
    int getMaximalWork(int maxApplications, long timeout);

    /// Checks if it is allowed to apply the next rule on the selected [ProofGoal] chosen by
    /// the [GoalChooser] before it is applied. If it is not allowed the apply strategy
    /// will stop.
    ///
    /// @param goal The current [ProofGoal] on which the next rule will be applied.
    /// @param maxApplications The defined maximal number of rules to apply.
    /// @param timeout The defined timeout in ms or `-1` if disabled.
    /// @param startTime The timestamp when the proof search (apply strategy) has started, computed
    /// via [#currentTimeMillis()]
    /// @param countApplied The number of already applied rules.
    /// @return `true` rule application is allowed, `false` rule application is not
    /// allowed so stop apply strategy
    boolean isGoalAllowed(G goal, int maxApplications, long timeout, long startTime,
            int countApplied);

    /// Returns the reason why the previous check via
    /// [#isGoalAllowed(ProofGoal,int,long,long,int)] has
    /// stopped the apply strategy.
    ///
    /// @param goal The current [ProofGoal] on which the next rule will be applied.
    /// @param maxApplications The defined maximal number of rules to apply.
    /// @param timeout The defined timeout in ms or `-1` if disabled.
    /// @param startTime The timestamp when the apply strategy has started,
    /// computed via [#currentTimeMillis()]
    /// @param countApplied The number of already applied rules.
    /// @return description of the reason why automatic proof search has stopped
    String getGoalNotAllowedMessage(G goal, int maxApplications, long timeout,
            long startTime, int countApplied);

    /// Checks after each applied rule if more rules should be applied or if the strategy should
    /// stop.
    ///
    /// @param maxApplications The defined maximal number of rules to apply.
    /// @param timeout The defined timeout in ms or `-1` if disabled.
    /// @param startTime The timestamp when the apply strategy has started, computed via
    /// [#currentTimeMillis()]
    /// @param countApplied The number of already applied rules.
    /// @param singleRuleApplicationInfo An optional [SingleRuleApplicationInfo].
    /// @return `true` stop strategy, `false` continue strategy and apply next rule.
    boolean shouldStop(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo);

    /// Returns a human-readable message which explains why the previous
    /// [#shouldStop(int,long,long,int,SingleRuleApplicationInfo)]
    /// has stopped the strategy.
    ///
    /// @param maxApplications The defined maximal number of rules to apply.
    /// @param timeout The defined timeout in ms or `-1` if disabled.
    /// @param startTime The timestamp when the apply strategy has started, computed via
    /// [#currentTimeMillis()]
    /// @param countApplied The number of already applied rules.
    /// @param singleRuleApplicationInfo An optional [SingleRuleApplicationInfo].
    /// @return The human-readable message which explains the stop reason.
    String getStopMessage(int maxApplications, long timeout, long startTime,
            int countApplied, SingleRuleApplicationInfo singleRuleApplicationInfo);
}
