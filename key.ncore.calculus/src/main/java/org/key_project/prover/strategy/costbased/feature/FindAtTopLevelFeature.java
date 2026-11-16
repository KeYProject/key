/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Feature that returns zero iff the find position of a taclet application is a formula of the
/// sequent, and infinity otherwise. It returns zero for a rule application that is not a taclet.
@StableCost
public class FindAtTopLevelFeature extends BinaryTacletAppFeature {
    private static final Feature INSTANCE = new FindAtTopLevelFeature();

    private FindAtTopLevelFeature() {}

    public static Feature getInstance() {
        return INSTANCE;
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, ProofGoal<?> goal,
            MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";
        return pos.isTopLevel();
    }
}
