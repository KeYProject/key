/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.util.Arrays;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;
import de.uka.ilkd.key.util.Debug;

/**
 * A feature that computes the sum of a given list (vector) of features
 */
public class SumFeature implements Feature {

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        // We require that there is at least one feature (in method
        // <code>createSum</code>)
        RuleAppCost res = features[0].computeCost(app, pos, goal);

        for (int i = 1; i < features.length && !(res instanceof TopRuleAppCost); i++) {
            res = res.add(features[i].computeCost(app, pos, goal));
        }

        return res;
    }

    private SumFeature(Feature[] p_features) {
        features = p_features;
    }

    static void flatten(Feature[] sumF, LinkedHashSet<Feature> p_features) {
        for (Feature f : sumF) {
            if (f instanceof SumFeature) {
                flatten(((SumFeature) f).features, p_features);
            } else {
                p_features.add(f);
            }
        }
    }

    public static Feature createSum(Feature... fs) {
        Debug.assertFalse(fs.length == 0, "Cannot compute the sum of zero features");

        if (fs.length == 1) {
            return fs[0];
        }
        LinkedHashSet<Feature> featureSet = new LinkedHashSet<>();
        flatten(fs, featureSet);

        return new SumFeature(featureSet.toArray(new Feature[fs.length]));
    }

    private final Feature[] features;

    @Override
    public String toString() {
        return "SumFeature: " + Arrays.toString(features);
    }
}
