/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

/**
 * Abstract superclass for features that have either zero cost or top cost.
 */
public abstract class BinaryFeature implements Feature<Goal> {

    protected BinaryFeature() {}

    /** Constant that represents the boolean value true */
    public static final RuleAppCost ZERO_COST = NumberRuleAppCost.getZeroCost();
    /** Constant that represents the boolean value false */
    public static final RuleAppCost TOP_COST = TopRuleAppCost.INSTANCE;

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        return filter(app, pos, goal, mState) ? ZERO_COST : TOP_COST;
    }

    /**
     * Compute whether the result of the feature is zero (<code>true</code>) or infinity
     * (<code>false</code>)
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @param mState mutable state needed for feature computation
     * @return true iff the result of the feature is supposed to be zero.
     */
    protected abstract boolean filter(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState);

}
