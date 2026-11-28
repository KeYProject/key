/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.engine;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.ProofObject;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

/// Interface to be implemented by classes in order to customize the goal selection strategy of the
/// automatic prover environment.
public interface GoalChooser<G extends ProofGoal<G>> {

    /// Initialise this GoalChooser for use with a given Proof and a list of goals.
    ///
    /// @param p_proof the proof object
    /// @param p_goals the initial list of goals
    void init(@Nullable ProofObject<G> p_proof, @Nullable ImmutableList<G> p_goals);

    /// @return the next goal a taclet should be applied to
    @Nullable
    G getNextGoal();

    /// Remove goal from selectedList (e.g. no taclet can be applied to goal)
    void removeGoal(G goal);

    /// The given node has become an internal node of the proof tree, and the children of the node
    /// are the given goals
    ///
    /// @param goal the goal which has been replaced by the new goals; it is used to identify
    /// outdated goals managed
    /// by this chooser
    ///
    /// @param newGoals the goals associated with node's children
    void updateGoalList(@Nullable G goal, @NonNull ImmutableList<G> newGoals);

}
