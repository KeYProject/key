/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.rulefilter.AnyRuleSetTacletFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;

/**
 * This feature checks if a rule may be applied automatically. Currently, this does not apply to
 * rules which are not member of any rule set.
 */
public class AutomatedRuleFeature<Goal extends ProofGoal<@NonNull Goal>>
        extends BinaryFeature<Goal> {

    private static final Feature<?> INSTANCE = new AutomatedRuleFeature<>();

    private AutomatedRuleFeature() {}

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature<Goal> getInstance() {
        // noinspection unchecked
        return (Feature<Goal>) INSTANCE;
    }

    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return !(app.rule() instanceof Taclet)
                || AnyRuleSetTacletFilter.INSTANCE.filter(app.rule());
    }
}
