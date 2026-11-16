/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.quantifierHeuristics;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

/// Maps the cost that `costFeature` predicts for a quantifier instance to the cost of the
/// instantiation. The cost 0 maps to -3000 and the cost 1 maps to 0. Another finite cost maps to
/// that cost plus 200 if `allowSplitting` returns zero, and to infinity otherwise.
public class InstantiationCostScalerFeature
        implements Feature {
    private final Feature costFeature;
    private final Feature allowSplitting;

    private static final RuleAppCost ONE_COST = NumberRuleAppCost.create(1);
    private static final RuleAppCost MINUS_3000_COST = NumberRuleAppCost.create(-3000);

    private InstantiationCostScalerFeature(Feature costFeature,
            Feature allowSplitting) {
        this.costFeature = costFeature;
        this.allowSplitting = allowSplitting;
    }

    public static Feature create(Feature costFeature, Feature allowSplitting) {
        return new InstantiationCostScalerFeature(costFeature, allowSplitting);
    }

    @Override
    public RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, ProofGoal<?> goal,
            MutableState mState) {
        final RuleAppCost cost = costFeature.computeCost(app, pos, goal, mState);

        if (cost.equals(NumberRuleAppCost.getZeroCost())) {
            return MINUS_3000_COST;
        }
        if (cost.equals(ONE_COST)) {
            return NumberRuleAppCost.getZeroCost();
        }

        final RuleAppCost as = allowSplitting.computeCost(app, pos, goal, mState);
        if (!as.equals(NumberRuleAppCost.getZeroCost())) {
            return TopRuleAppCost.INSTANCE;
        }
        if (cost.equals(TopRuleAppCost.INSTANCE)) {
            return TopRuleAppCost.INSTANCE;
        }

        assert cost instanceof NumberRuleAppCost : "Can only handle LongRuleAppCost";

        final NumberRuleAppCost longCost = (NumberRuleAppCost) cost;
        return NumberRuleAppCost.create(longCost.getValue() + 200);
    }
}
