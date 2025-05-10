/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableList;

/**
 * This feature checks that the position of application is not contained in the if-formulas. If the
 * rule application is admissible, zero is returned.
 */
public class NoSelfApplicationFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new NoSelfApplicationFeature();

    private NoSelfApplicationFeature() {}

    @Override
    protected boolean filter(TacletApp p_app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null
                : "NoSelfApplicationFeature: Need to know the position of the application of the taclet";

        if (!p_app.assumesInstantionsComplete()) {
            return true;
        }

        ImmutableList<AssumesFormulaInstantiation> assumesInstantiations =
            p_app.assumesFormulaInstantiations();

        assert assumesInstantiations != null && !assumesInstantiations.isEmpty()
                : "NoSelfApplicationFeature: Need to know the equation the taclet is used with";

        boolean noSelfApplication = true;
        for (var assumesInstantiation : assumesInstantiations) {
            noSelfApplication =
                noSelfApplication
                        && assumesInstantiation.getSequentFormula() != pos.sequentFormula();
        }
        return noSelfApplication;
    }

}
