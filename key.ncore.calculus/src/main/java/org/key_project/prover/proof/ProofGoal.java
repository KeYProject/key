/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.strategy.RuleApplicationManager;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/// Interface for proof goals of a sequent proof.
///
/// @param <G> the type of the concrete realization of the proof goal
public interface ProofGoal<G extends @Nullable ProofGoal<G>> {
    /// The proof object to which this goal belongs.
    ///
    /// @return proof object with which this goal is associated
    ProofObject<G> proof();

    /// The sequent to which this goal points and that should be
    /// proven valid.
    ///
    /// @return the sequent associated with this goal
    Sequent sequent();

    /// Perform the provided rule application on this goal and return
    /// the new goal(s), if any.
    ///
    /// @param ruleApp the [RuleApp] to be applied
    /// @return new goal(s)
    @Nullable
    ImmutableList<G> apply(final RuleApp ruleApp);

    /// returns the prover component responsible for providing the next
    /// rule application to be applied on this goal
    ///
    /// @return the RuleApplicationManager selecting the next rule
    /// application to be applied on this goal
    RuleApplicationManager<G> getRuleAppManager();

    /// returns the current time of this goal
    /// the only requirement is that a goal that is a successor of this goal returns
    /// a larger number
    /// @return long with current time of goal
    long getTime();
}
