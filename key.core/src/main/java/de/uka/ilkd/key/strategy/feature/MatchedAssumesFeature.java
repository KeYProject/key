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
 * Binary features that returns zero iff the if-formulas of a Taclet are instantiated or the Taclet
 * does not have any if-formulas.
 */
public final class MatchedAssumesFeature extends BinaryTacletAppFeature {

    public static final Feature INSTANCE = new MatchedAssumesFeature();

    private MatchedAssumesFeature() {}

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return app.assumesInstantionsComplete();
    }

}
