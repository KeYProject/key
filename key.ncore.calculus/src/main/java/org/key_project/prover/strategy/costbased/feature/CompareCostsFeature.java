/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;

public abstract class CompareCostsFeature
        extends BinaryFeature {

    protected final Feature a, b;

    private CompareCostsFeature(Feature a, Feature b) {
        this.a = a;
        this.b = b;
    }

    public static Feature less(Feature a, Feature b) {
        return new CompareCostsFeature(a, b) {
            @Override
            protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
                    PosInOccurrence pos, Goal goal, MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) < 0;
            }
        };
    }

    public static Feature leq(Feature a, Feature b) {
        return new CompareCostsFeature(a, b) {
            @Override
            protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
                    PosInOccurrence pos, Goal goal, MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) <= 0;
            }
        };
    }

    public static Feature eq(Feature a, Feature b) {
        return new CompareCostsFeature(a, b) {
            @Override
            protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
                    PosInOccurrence pos, Goal goal, MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .equals(b.computeCost(app, pos, goal, mState));
            }
        };
    }

}
