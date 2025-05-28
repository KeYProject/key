/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.rulefilter.RuleFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;

import org.jspecify.annotations.NonNull;

/// A feature that evaluates one of two given features, depending on the result of a
/// <code>RuleFilter</code>
public class ConditionalFeature implements Feature {

    private ConditionalFeature(RuleFilter p_cond, Feature p_thenFeature,
            Feature p_elseFeature) {
        cond = p_cond;
        thenFeature = p_thenFeature;
        elseFeature = p_elseFeature;
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        if (cond.filter(app.rule())) {
            return thenFeature.computeCost(app, pos, goal, mState);
        } else {
            return elseFeature.computeCost(app, pos, goal, mState);
        }
    }

    /// @param cond the filter that decides which value is to be returned
    /// @param thenValue the value of the feature, if <code>filter</code> returns true
    public static Feature createConditional(RuleFilter cond, RuleAppCost thenValue) {
        return createConditional(cond, ConstFeature.createConst(thenValue));
    }

    /// @param cond the filter that decides which value is to be returned
    /// @param thenValue the value of the feature, if <code>filter</code> returns true
    /// @param elseValue the value of the feature, if <code>filter</code> returns false
    public static Feature createConditional(RuleFilter cond, RuleAppCost thenValue,
            RuleAppCost elseValue) {
        return createConditional(cond, ConstFeature.createConst(thenValue),
            ConstFeature.createConst(elseValue));
    }

    /// @param cond the filter that decides which value is to be returned
    /// @param thenFeature the feature that is evaluted, if <code>filter</code> returns true returns
    /// false
    public static Feature createConditional(
            RuleFilter cond, Feature thenFeature) {
        return createConditional(cond, thenFeature, NumberRuleAppCost.getZeroCost());
    }

    /// @param cond the filter that decides which value is to be returned
    /// @param thenFeature the feature that is evaluted, if <code>filter</code> returns true
    /// @param elseValue the value of the feature, if <code>filter</code> returns false
    public static Feature createConditional(
            RuleFilter cond, Feature thenFeature,
            RuleAppCost elseValue) {
        return createConditional(cond, thenFeature, ConstFeature.createConst(elseValue));
    }

    /// @param cond the filter that decides which value is to be returned
    /// @param thenFeature the feature that is evaluted, if <code>filter</code> returns true
    /// @param elseFeature the feature that is evaluted, if <code>filter</code> returns false
    public static Feature createConditional(RuleFilter cond, Feature thenFeature,
            Feature elseFeature) {
        return new ConditionalFeature(cond, thenFeature, elseFeature);
    }

    /// The filter that decides which sub-feature is to be evaluated
    private final RuleFilter cond;

    /// The feature for positive results of <code>filter</code>
    private final Feature thenFeature;

    /// The feature for negative results of <code>filter</code>
    private final Feature elseFeature;
}
