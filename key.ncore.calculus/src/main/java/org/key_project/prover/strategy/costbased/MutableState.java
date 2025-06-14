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
