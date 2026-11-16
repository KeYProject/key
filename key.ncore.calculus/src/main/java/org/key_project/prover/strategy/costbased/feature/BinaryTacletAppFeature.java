/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

/// Abstract superclass for features of TacletApps that have either zero or top cost.
public abstract class BinaryTacletAppFeature extends BinaryFeature {
    private final boolean nonTacletValue;

    protected BinaryTacletAppFeature() {
        nonTacletValue = true;
    }

    /// @param p_nonTacletValue the value that is to be returned should the feature be applied to a
    /// rule that is not a taclet
    protected BinaryTacletAppFeature(boolean p_nonTacletValue) {
        nonTacletValue = p_nonTacletValue;
    }

    @Override
    final protected boolean filter(RuleApp app,
            PosInOccurrence pos,
            ProofGoal<?> goal, MutableState mState) {
        if (app instanceof ITacletApp tacletApp) {
            return filter(tacletApp, pos, goal, mState);
        }
        return nonTacletValue;
    }

    /// Compute whether the result of the feature is zero (`true`) or infinity
    /// (`false`)
    ///
    /// @param app the ITacletApp
    /// @param pos position where `app` is to be applied
    /// @param goal the goal on which `app` is to be applied
    /// @param mState the MutableState used to store modifiable information
    /// @return true iff the result of the feature is supposed to be zero.
    protected abstract boolean filter(ITacletApp app, PosInOccurrence pos, ProofGoal<?> goal,
            MutableState mState);
}
