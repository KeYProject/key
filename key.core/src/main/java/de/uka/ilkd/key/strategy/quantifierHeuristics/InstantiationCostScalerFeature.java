/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;

public class InstantiationCostScalerFeature implements Feature {

    private final Feature costFeature;
    private final Feature allowSplitting;

    private static final RuleAppCost ONE_COST = NumberRuleAppCost.create(1);
    private static final RuleAppCost MINUS_3000_COST = NumberRuleAppCost.create(-3000);

    private InstantiationCostScalerFeature(Feature costFeature, Feature allowSplitting) {
        this.costFeature = costFeature;
        this.allowSplitting = allowSplitting;
    }

    public static Feature create(Feature costFeature, Feature allowSplitting) {
        return new InstantiationCostScalerFeature(costFeature, allowSplitting);
    }

    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {

        final RuleAppCost cost = costFeature.computeCost(app, pos, goal);

        if (cost.equals(NumberRuleAppCost.getZeroCost())) {
            return MINUS_3000_COST;
        }
        if (cost.equals(ONE_COST)) {
            return NumberRuleAppCost.getZeroCost();
        }

        final RuleAppCost as = allowSplitting.computeCost(app, pos, goal);
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
