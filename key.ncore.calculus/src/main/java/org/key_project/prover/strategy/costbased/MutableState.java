/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased;

import java.util.HashMap;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.strategy.costbased.feature.instantiator.BackTrackingManager;
import org.key_project.prover.strategy.costbased.feature.instantiator.ChoicePoint;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;

import org.jspecify.annotations.NonNull;

/**
 * <p>
 * Realizes a variable bank for strategy features such that each feature
 * computation can be done in parallel.
 * </p>
 * <p>
 * When the strategy computes the costs for a {@link RuleApp} it creates
 * a new MutableState object and passes it on. This is then used by features
 * to query for the value of {@link TermBuffer}s.
 * </p>
 * <p>
 * This mutable state should not be abused and strategy features should be stateless.
 * </p>
 *
 * @author Richard Bubel
 */
public class MutableState {

    /** maps a term buffer to its value */
    private HashMap<TermBuffer<?>, Term> content;

    /** manages backtracking for features that create {@link ChoicePoint}s */
    private BackTrackingManager btManager;

    /**
     * assign the given {@link TermBuffer} the provided value
     *
     * @param v the {@link TermBuffer}
     * @param value the Term which is assigned as the value
     */
    public <Goal extends ProofGoal<@NonNull Goal>> void assign(TermBuffer<Goal> v, Term value) {
        if (content == null) {
            content = new HashMap<>();
        }
        content.put(v, value);
    }

    /**
     * retrieves the current value of the given {@link TermBuffer}
     *
     * @param v the TermBuffer whose value is asked for
     * @return the current value of the {@link TermBuffer} or {@code null} if there is none
     */
    public <Goal extends ProofGoal<@NonNull Goal>> Term read(TermBuffer<Goal> v) {
        if (content == null) {
            return null;
        }
        return content.get(v);
    }

    /**
     * returns the backtracking manager to access {@link ChoicePoint}s
     *
     * @return the backtracking manager
     */
    public BackTrackingManager getBacktrackingManager() {
        if (btManager == null) {
            btManager = new BackTrackingManager();
        }
        return btManager;
    }
}
