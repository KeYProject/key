/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Binary features that returns zero iff the assumes-formulas of a Taclet are instantiated or the
/// Taclet
/// does not have any assumes-formulas.
@StableCost
public final class MatchedAssumesFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {
    public static <GOAL extends ProofGoal<GOAL>> MatchedAssumesFeature<GOAL> create() {
        return new MatchedAssumesFeature<>();
    }

    private MatchedAssumesFeature() {}

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal,
            MutableState mState) {
        return app.assumesInstantionsComplete();
    }
}
