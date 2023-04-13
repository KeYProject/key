package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Feature that computes the age of the goal (i.e. total number of rules applications that have been
 * performed at the goal) to which a rule is supposed to be applied
 */
public class AgeFeature implements Feature {

    public static final Feature INSTANCE = new AgeFeature();

    private AgeFeature() {}

    public long computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return goal.getTime();
        // return LongRuleAppCost.create ( goal.getTime() / goal.sequent ().size () );
        // return LongRuleAppCost.create ( (long)Math.sqrt ( goal.getTime () ) );
    }

}
