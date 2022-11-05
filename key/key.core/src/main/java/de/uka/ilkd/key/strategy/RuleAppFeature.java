package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Generic interface for evaluating the cost of a RuleApp with regard to a specific feature (like
 * term size, ...)
 */
public interface RuleAppFeature {

    /**
     * Evaluate the cost of a RuleApp.
     */
    public long cost(RuleApp app, Goal goal);

}
