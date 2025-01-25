/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Arrays;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.util.Debug;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

/**
 * A feature that computes the sum of a given list (vector) of features
 */
public class SumFeature implements Feature<Goal> {

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        // We require that there is at least one feature (in method
        // <code>createSum</code>)
        RuleAppCost res = features[0].computeCost(app, pos, goal, mState);

        for (int i = 1; i < features.length && !(res instanceof TopRuleAppCost); i++) {
            res = res.add(features[i].computeCost(app, pos, goal, mState));
        }

        return res;
    }

    private SumFeature(Feature<Goal>[] p_features) {
        features = p_features;
    }

    static void flatten(Feature<Goal>[] sumF, LinkedHashSet<Feature<Goal>> p_features) {
        for (Feature<Goal> f : sumF) {
            if (f instanceof SumFeature sumFeature) {
                flatten(sumFeature.features, p_features);
            } else {
                p_features.add(f);
            }
        }
    }

    @SafeVarargs
    public static Feature<Goal> createSum(Feature<Goal>... fs) {
        Debug.assertFalse(fs.length == 0, "Cannot compute the sum of zero features");

        if (fs.length == 1) {
            return fs[0];
        }
        LinkedHashSet<Feature<Goal>> featureSet = new LinkedHashSet<>();
        flatten(fs, featureSet);

        return new SumFeature(featureSet.<Feature<Goal>>toArray(new Feature[fs.length]));
    }

    private final Feature<Goal>[] features;

    @Override
    public String toString() {
        return "SumFeature: " + Arrays.toString(features);
    }
}
