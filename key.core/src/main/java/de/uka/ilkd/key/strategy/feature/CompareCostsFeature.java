/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;

public abstract class CompareCostsFeature extends BinaryFeature {

    protected final Feature<Goal> a, b;

    private CompareCostsFeature(Feature<Goal> a, Feature<Goal> b) {
        this.a = a;
        this.b = b;
    }

    public static Feature<Goal> less(Feature<Goal> a, Feature<Goal> b) {
        return new CompareCostsFeature(a, b) {
            protected boolean filter(org.key_project.prover.rules.RuleApp app, PosInOccurrence pos,
                    Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) < 0;
            }
        };
    }

    public static Feature<Goal> leq(Feature<Goal> a, Feature<Goal> b) {
        return new CompareCostsFeature(a, b) {
            protected boolean filter(org.key_project.prover.rules.RuleApp app, PosInOccurrence pos,
                    Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) <= 0;
            }
        };
    }

    public static Feature<Goal> eq(Feature<Goal> a, Feature<Goal> b) {
        return new CompareCostsFeature(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .equals(b.computeCost(app, pos, goal, mState));
            }
        };
    }

}
