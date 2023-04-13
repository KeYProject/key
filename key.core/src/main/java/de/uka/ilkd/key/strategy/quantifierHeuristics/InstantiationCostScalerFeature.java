package de.uka.ilkd.key.strategy.quantifierHeuristics;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;

public class InstantiationCostScalerFeature implements Feature {

    private final Feature costFeature;
    private final Feature allowSplitting;

    private static final long ONE_COST = 1;
    private static final long MINUS_3000_COST = -3000;

    private InstantiationCostScalerFeature(Feature costFeature, Feature allowSplitting) {
        this.costFeature = costFeature;
        this.allowSplitting = allowSplitting;
    }

    public static Feature create(Feature costFeature, Feature allowSplitting) {
        return new InstantiationCostScalerFeature(costFeature, allowSplitting);
    }

    public long computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        final long cost = costFeature.computeCost(app, pos, goal);

        if (cost == RuleAppCost.ZERO) {
            return MINUS_3000_COST;
        }
        if (cost == ONE_COST) {
            return RuleAppCost.ZERO;
        }

        final long as = allowSplitting.computeCost(app, pos, goal);
        if (!(as == RuleAppCost.ZERO)) {
            return RuleAppCost.MAX_VALUE;
        }
        if (cost == RuleAppCost.MAX_VALUE) {
            return RuleAppCost.MAX_VALUE;
        }

        return RuleAppCost.addRight(cost, 200);
    }

}
