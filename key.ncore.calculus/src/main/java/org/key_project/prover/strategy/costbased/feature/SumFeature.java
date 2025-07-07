/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.util.Arrays;
import java.util.LinkedHashSet;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;

import org.jspecify.annotations.NonNull;

/// A feature that computes the sum of a given list (vector) of features
public class SumFeature implements Feature {

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal,
            MutableState mState) {
        // We require that there is at least one feature (in method
        // <code>createSum</code>)
        RuleAppCost res = features[0].computeCost(app, pos, goal, mState);

        for (int i = 1; i < features.length && !(res instanceof TopRuleAppCost); i++) {
            res = res.add(features[i].computeCost(app, pos, goal, mState));
        }

        return res;
    }

    private SumFeature(Feature[] p_features) {
        features = p_features;
    }

    static <Goal extends ProofGoal<@NonNull Goal>> void flatten(Feature[] sumF,
            LinkedHashSet<Feature> p_features) {
        for (Feature f : sumF) {
            if (f instanceof SumFeature sumFeature) {
                flatten(sumFeature.features, p_features);
            } else {
                p_features.add(f);
            }
        }
    }

    @SafeVarargs
    public static <Goal extends ProofGoal<@NonNull Goal>> Feature createSum(
            Feature... fs) {
        assert fs.length != 0 : "Cannot compute the sum of zero features";

        if (fs.length == 1) {
            return fs[0];
        }
        LinkedHashSet<Feature> featureSet = new LinkedHashSet<>();
        flatten(fs, featureSet);

        // noinspection unchecked
        return new SumFeature(featureSet.<Feature>toArray(new Feature[0]));
    }

    private final Feature[] features;

    @Override
    public String toString() {
        return "SumFeature: " + Arrays.toString(features);
    }
}
