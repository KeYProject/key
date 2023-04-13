package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Costs for the {@link MergeRule}; cheap if the first statement in the chosen top-level formula is
 * a {@link MergePointStatement}, otherwise, infinitely expensive.
 *
 * @author Dominic Scheurer
 */
public class MergeRuleFeature implements Feature {
    public static final Feature INSTANCE = new MergeRuleFeature();

    private MergeRuleFeature() {
        // Singleton constructor
    }

    @Override
    public long computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term t = pos.subTerm();
        if (!pos.isTopLevel() || !t.containsJavaBlockRecursive()) {
            return RuleAppCost.MAX_VALUE;
        }

        return JavaTools.getActiveStatement(
            TermBuilder.goBelowUpdates(t).javaBlock()) instanceof MergePointStatement
                    ? 0
                    : RuleAppCost.MAX_VALUE;
    }

}
