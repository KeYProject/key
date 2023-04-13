package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Abstract superclass for features that have either zero cost or top cost.
 */
public abstract class BinaryFeature implements Feature {

    protected BinaryFeature() {}

    /** Constant that represents the boolean value true */
    public static final long ZERO_COST = RuleAppCost.ZERO;
    /** Constant that represents the boolean value false */
    public static final long TOP_COST = RuleAppCost.MAX_VALUE;

    public long computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return filter(app, pos, goal) ? ZERO_COST : TOP_COST;
    }

    /**
     * Compute whether the result of the feature is zero (<code>true</code>) or infinity
     * (<code>false</code>)
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return true iff the the result of the feature is supposed to be zero.
     */
    protected abstract boolean filter(RuleApp app, PosInOccurrence pos, Goal goal);

}
