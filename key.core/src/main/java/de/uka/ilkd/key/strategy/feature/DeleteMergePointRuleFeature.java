/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.recoderext.MergePointStatement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

/**
 * Costs for the {@link DeleteMergePointRule}; incredibly cheap if the previous rule application was
 * a {@link MergeRule} app, infinitely expensive otherwise. The alternative would be to always check
 * whether there's another {@link Goal} around with the same {@link MergePointStatement} (then we
 * may not delete), which is much more time intensive.
 *
 * @author Dominic Scheurer
 */
public class DeleteMergePointRuleFeature implements Feature {
    public static final Feature INSTANCE = new DeleteMergePointRuleFeature();

    private DeleteMergePointRuleFeature() {
        // Singleton constructor
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return goal.node().parent().getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                ? NumberRuleAppCost.create(-50000)
                : TopRuleAppCost.INSTANCE;
    }

}
