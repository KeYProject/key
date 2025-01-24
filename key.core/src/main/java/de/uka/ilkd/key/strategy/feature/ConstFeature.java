/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

/**
 * A feature that returns a constant value
 */
public class ConstFeature implements Feature<Goal> {
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        return val;
    }

    private ConstFeature(RuleAppCost p_val) {
        val = p_val;
    }

    public static Feature<Goal> createConst(RuleAppCost p_val) {
        return new ConstFeature(p_val);
    }

    public final RuleAppCost getValue() {
        return val;
    }

    private final RuleAppCost val;
}
