/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;

public abstract class CompareCostsFeature<Goal extends ProofGoal<@NonNull Goal>>
        extends BinaryFeature<Goal> {

    protected final Feature<Goal> a, b;

    private CompareCostsFeature(Feature<Goal> a, Feature<Goal> b) {
        this.a = a;
        this.b = b;
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature<Goal> less(Feature<Goal> a,
            Feature<Goal> b) {
        return new CompareCostsFeature<>(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos,
                    Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) < 0;
            }
        };
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature<Goal> leq(Feature<Goal> a,
            Feature<Goal> b) {
        return new CompareCostsFeature<>(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos,
                    Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) <= 0;
            }
        };
    }

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature<Goal> eq(Feature<Goal> a,
            Feature<Goal> b) {
        return new CompareCostsFeature<>(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .equals(b.computeCost(app, pos, goal, mState));
            }
        };
    }

}
