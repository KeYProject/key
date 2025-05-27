/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.recoderext.MergePointStatement;
import de.uka.ilkd.key.rule.merge.MergeRule;
import de.uka.ilkd.key.rule.merge.MergeRuleBuiltInRuleApp;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;

/**
 * Costs for the {@link DeleteMergePointRuleFeature}; incredibly cheap if the previous rule
 * application was
 * a {@link MergeRule} app, infinitely expensive otherwise. The alternative would be to always check
 * whether there's another {@link ProofGoal} around with the same {@link MergePointStatement} (then
 * we
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
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        return ((de.uka.ilkd.key.proof.Goal) goal).node().parent()
                .getAppliedRuleApp() instanceof MergeRuleBuiltInRuleApp
                        ? NumberRuleAppCost.create(-50000)
                        : TopRuleAppCost.INSTANCE;
    }

}
