/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Interface to be implemented by classes in order to customize the goal selection strategy of the
/// automatic prover environment.
public interface GoalChooser<P extends @Nullable ProofObject<@NonNull G>, G extends @Nullable ProofGoal<@NonNull G>> {

    /// Initialise this GoalChooser for use with a given Proof and a list of goals.
    ///
    /// @param p_proof *param p_goals the initial list of goals
    void init(@Nullable P p_proof, @Nullable ImmutableList<G> p_goals);

    /// @return the next goal a taclet should be applied to
    @Nullable
    G getNextGoal();

    /// Remove p_goal from selectedList (e.g. no taclet can be applied to p_goal)
    void removeGoal(G p_goal);

    /// The given node has become an internal node of the proof tree, and the children of the node
    /// are the given goals
    ///
    /// @param previousGoalContent the content of the goal which has been replaced by the new goals;
    /// it is used to identify outdated goals managed by this chooser (a typical argument is
    /// the node of proof tree which is now an inner node)
    ///
    /// @param newGoals the goals associated with node's children
    void updateGoalList(@Nullable Object previousGoalContent, @NonNull ImmutableList<G> newGoals);

}
