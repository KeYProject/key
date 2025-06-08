/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;

/**
 * Feature that computes the age of the goal (i.e. total number of rules applications that have been
 * performed at the goal) to which a rule is supposed to be applied
 */
public class AgeFeature implements Feature {

    public static final Feature INSTANCE = new AgeFeature();

    private AgeFeature() {}

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        return NumberRuleAppCost.create(((de.uka.ilkd.key.proof.Goal) goal).getTime());
        // return LongRuleAppCost.create ( goal.getTime() / goal.sequent ().size () );
        // return LongRuleAppCost.create ( (long)Math.sqrt ( goal.getTime () ) );
    }

}
