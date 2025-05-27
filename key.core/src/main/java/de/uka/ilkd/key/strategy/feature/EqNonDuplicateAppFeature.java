/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;


/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed.
 * Contrary to <code>NonDuplicateAppFeature</code>, this feature is also able to handle failing
 * meta-constructs correctly (these constructs return equal, but not identical formulas in case of a
 * failure), but is less efficient.
 */
public class EqNonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new EqNonDuplicateAppFeature();

    private EqNonDuplicateAppFeature() {}

    @Override
    public boolean filter(TacletApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        if (!app.assumesInstantionsComplete()) {
            return true;
        }

        return noDuplicateFindTaclet(app, pos, goal);
    }

    @Override
    protected boolean comparePio(TacletApp newApp, TacletApp oldApp,
            PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        return oldPio.eqEquals(newPio);
    }
}
