/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

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
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term t = pos.subTerm();
        if (!pos.isTopLevel() || !t.containsJavaBlockRecursive()) {
            return TopRuleAppCost.INSTANCE;
        }

        return JavaTools.getActiveStatement(
            TermBuilder.goBelowUpdates(t).javaBlock()) instanceof MergePointStatement
                    ? NumberRuleAppCost.create(0)
                    : TopRuleAppCost.INSTANCE;
    }

}
