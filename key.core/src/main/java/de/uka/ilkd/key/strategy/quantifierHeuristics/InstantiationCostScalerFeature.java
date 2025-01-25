/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

public class InstantiationCostScalerFeature implements Feature<Goal> {

    private final Feature<Goal> costFeature;
    private final Feature<Goal> allowSplitting;

    private static final RuleAppCost ONE_COST = NumberRuleAppCost.create(1);
    private static final RuleAppCost MINUS_3000_COST = NumberRuleAppCost.create(-3000);

    private InstantiationCostScalerFeature(Feature<Goal> costFeature,
            Feature<Goal> allowSplitting) {
        this.costFeature = costFeature;
        this.allowSplitting = allowSplitting;
    }

    public static Feature<Goal> create(Feature<Goal> costFeature, Feature<Goal> allowSplitting) {
        return new InstantiationCostScalerFeature(costFeature, allowSplitting);
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
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
