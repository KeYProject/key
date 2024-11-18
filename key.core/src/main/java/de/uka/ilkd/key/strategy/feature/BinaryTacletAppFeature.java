/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.sequent.PosInOccurrence;

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
    final protected boolean filter(RuleApp app, PosInOccurrence pos,
            Goal goal,
            MutableState mState) {
        if (app instanceof TacletApp) {
            return filter((TacletApp) app, pos, goal, mState);
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
