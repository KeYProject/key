/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

/// A feature that returns a constant value
public class ConstFeature implements Feature {

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        return val;
    }

    private ConstFeature(RuleAppCost p_val) {
        val = p_val;
    }

    public static Feature createConst(RuleAppCost p_val) {
        return new ConstFeature(p_val);
    }

    public final RuleAppCost getValue() {
        return val;
    }

    private final RuleAppCost val;
}
