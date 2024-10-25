/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.ncore.sequent.PosInOccurrence;


/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed
 */
public class NonDuplicateAppFeature extends AbstractNonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppFeature();

    public boolean filter(TacletApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        if (!app.ifInstsComplete()) {
            return true;
        }

        return noDuplicateFindTaclet(app, pos, goal);
    }

    protected boolean comparePio(TacletApp newApp, TacletApp oldApp,
            PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        return oldPio.equals(newPio);
    }
}
