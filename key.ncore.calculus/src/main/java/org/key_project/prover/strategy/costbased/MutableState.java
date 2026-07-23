/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased;

import java.util.HashMap;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.strategy.costbased.feature.instantiator.BackTrackingManager;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

///
/// Realizes a variable bank for strategy features such that each feature
/// computation can be done in parallel.
///
///
/// When the strategy computes the costs for a [RuleApp] it creates
/// a new MutableState object and passes it on. This is then used by features
/// to query for the value of [TermBuffer]s.
///
///
/// This mutable state should not be abused and strategy features should be stateless.
///
///
/// @author Richard Bubel
public class MutableState {

    /// maps a term buffer to its value
    private final HashMap<TermBuffer<?>, @Nullable Term> content = HashMap.newHashMap(32);

    /// The branch currently chosen at each `OneOfCP`-style choice point, keyed by the choice point.
    /// This state belongs to a single feature-term evaluation, so it is kept here (per evaluation)
    /// rather than in a field of the choice point: one strategy -- hence one feature tree -- is
    /// shared by all goals, so a field on the choice point would be written concurrently by the
    /// multi-core prover's worker threads.
    private final HashMap<Object, Integer> choicePointIndex = HashMap.newHashMap(8);

    /// manages backtracking for features that create [ChoicePoint]s
    private @MonotonicNonNull BackTrackingManager btManager;

    /// assign the given [TermBuffer] the provided value
    ///
    /// @param v the [TermBuffer]
    /// @param value the Term which is assigned as the value
    public <Goal extends ProofGoal<Goal>> void assign(@NonNull TermBuffer<Goal> v,
            @Nullable Term value) {
        content.put(v, value);
    }

    /// retrieves the current value of the given [TermBuffer]
    ///
    /// @param v the TermBuffer whose value is asked for
    /// @return the current value of the [TermBuffer] or `null` if there is none
    public <Goal extends @NonNull ProofGoal<Goal>> @Nullable Term read(TermBuffer<Goal> v) {
        return content.get(v);
    }

    /// records which branch a choice point has chosen in this evaluation
    ///
    /// @param choicePoint the choice point (its own identity is the key)
    /// @param index the chosen branch
    public void setChoicePointIndex(Object choicePoint, int index) {
        choicePointIndex.put(choicePoint, index);
    }

    /// the branch chosen by the given choice point in this evaluation
    ///
    /// @param choicePoint the choice point
    /// @return the chosen branch, or 0 if none has been chosen yet
    public int getChoicePointIndex(Object choicePoint) {
        final Integer index = choicePointIndex.get(choicePoint);
        return index == null ? 0 : index;
    }

    /// returns the backtracking manager to access [ChoicePoint]s
    ///
    /// @return the backtracking manager
    public @Nullable BackTrackingManager getBacktrackingManager() {
        if (btManager == null) {
            btManager = new BackTrackingManager();
        }
        return btManager;
    }
}
