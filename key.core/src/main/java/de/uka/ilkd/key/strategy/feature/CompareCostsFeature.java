/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

import org.jspecify.annotations.NonNull;

public abstract class CompareCostsFeature extends BinaryFeature {

    protected final Feature a, b;

    private CompareCostsFeature(Feature a, Feature b) {
        this.a = a;
        this.b = b;
    }

    public static @NonNull Feature less(Feature a, Feature b) {
        return new CompareCostsFeature(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) < 0;
            }
        };
    }

    public static @NonNull Feature leq(Feature a, Feature b) {
        return new CompareCostsFeature(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .compareTo(b.computeCost(app, pos, goal, mState)) <= 0;
            }
        };
    }

    public static @NonNull Feature eq(Feature a, Feature b) {
        return new CompareCostsFeature(a, b) {
            protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal,
                    MutableState mState) {
                return a.computeCost(app, pos, goal, mState)
                        .equals(b.computeCost(app, pos, goal, mState));
            }
        };
    }

}
