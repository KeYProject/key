/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.rule.Taclet;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;

/**
 * Feature that returns the number of branches for a given taclet application Size of "assumes"
 * sequents is currently not considered
 */
public class CountBranchFeature implements Feature {

    public static final Feature INSTANCE = new CountBranchFeature();

    private CountBranchFeature() {
    }

    /**
     * Compute the cost of a RuleApp.
     *
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @param mState
     * @return the cost of <code>app</code>
     */
    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal,
            MutableState mState) {
        if (app.rule() instanceof Taclet tac) {
            final long branches = tac.goalTemplates().size();
            return NumberRuleAppCost.create(branches);
        }
        return NumberRuleAppCost.getZeroCost();
    }
}
