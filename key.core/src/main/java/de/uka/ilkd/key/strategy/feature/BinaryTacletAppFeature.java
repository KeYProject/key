/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;

import org.jspecify.annotations.NonNull;

/**
 * Abstract superclass for features of TacletApps that have either zero or top cost.
 */
public abstract class BinaryTacletAppFeature extends BinaryFeature {

    private final boolean nonTacletValue;

    protected BinaryTacletAppFeature() {
        nonTacletValue = true;
    }

    /**
     * @param p_nonTacletValue the value that is to be returned should the feature be applied to a
     *        rule that is not a taclet
     */
    protected BinaryTacletAppFeature(boolean p_nonTacletValue) {
        nonTacletValue = p_nonTacletValue;
    }

    @Override
    final protected <PGoal extends ProofGoal<@NonNull PGoal>> boolean filter(RuleApp app,
            PosInOccurrence pos,
            PGoal goal, MutableState mState) {
        if (app instanceof TacletApp tacletApp) {
            return filter(tacletApp, pos, (Goal) goal, mState);
        }
        return nonTacletValue;
    }

    /**
     * Compute whether the result of the feature is zero (<code>true</code>) or infinity
     * (<code>false</code>)
     *
     * @param app the TacletApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @param mState the MutableState used to store modifiable information
     * @return true iff the the result of the feature is supposed to be zero.
     */
    protected abstract boolean filter(TacletApp app, PosInOccurrence pos, Goal goal,
            MutableState mState);
}
