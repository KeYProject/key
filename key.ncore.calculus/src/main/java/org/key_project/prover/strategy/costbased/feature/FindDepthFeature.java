/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;


/// A feature that computes the depth of the find-position of a taclet (top-level positions have
/// depth zero or if not a find taclet)
///
/// TODO: eliminate this class and use term features instead
public class FindDepthFeature implements Feature {

    private static final Feature INSTANCE = new FindDepthFeature();

    public static Feature getInstance() {
        return INSTANCE;
    }

    private FindDepthFeature() {}

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        // assert pos != null : "Feature is only applicable to rules with find";
        return NumberRuleAppCost.create(pos == null ? 0 : pos.depth());
    }

}
