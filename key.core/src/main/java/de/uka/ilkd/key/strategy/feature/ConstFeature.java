package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * A feature that returns a constant value
 */
public class ConstFeature implements Feature {
    public long computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return val;
    }

    private ConstFeature(long p_val) {
        val = p_val;
    }

    public static Feature createConst(long p_val) {
        return new ConstFeature(p_val);
    }

    public final long getValue() {
        return val;
    }

    private final long val;
}
