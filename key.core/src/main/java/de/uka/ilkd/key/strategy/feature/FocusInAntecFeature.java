/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;

public class FocusInAntecFeature extends BinaryFeature {

    private FocusInAntecFeature() {}

    public static final Feature INSTANCE = new FocusInAntecFeature();

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";
        return pos.isInAntec();
    }
}
