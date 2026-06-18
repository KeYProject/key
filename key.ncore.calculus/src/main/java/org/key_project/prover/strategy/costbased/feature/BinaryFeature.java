/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;

import org.jspecify.annotations.NonNull;

/// Abstract superclass for features that have either zero cost or top cost.
public abstract class BinaryFeature
        implements Feature {

    protected BinaryFeature() {}

    /// Constant that represents the boolean value true
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();
    /// Constant that represents the boolean value false
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos,
            Goal goal, MutableState mState) {
        return filter(app, pos, goal, mState) ? ZERO_COST : TOP_COST;
    }

    /// Compute whether the result of the feature is zero (<code>true</code>) or infinity
    /// (<code>false</code>)
    ///
    /// @param app the RuleApp
    /// @param pos position where <code>app</code> is to be applied
    /// @param goal the goal on which <code>app</code> is to be applied
    /// @param mState mutable state needed for feature computation
    /// @return true iff the result of the feature is supposed to be zero.
    protected abstract <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
            PosInOccurrence pos, Goal goal,
            MutableState mState);

}
