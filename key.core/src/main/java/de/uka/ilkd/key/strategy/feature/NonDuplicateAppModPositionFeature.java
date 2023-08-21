/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;

import org.key_project.util.collection.ImmutableList;


/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed
 */
public class NonDuplicateAppModPositionFeature extends NonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppModPositionFeature();

    @Override
    public boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        if (!app.ifInstsComplete()) {
            return true;
        }

        return noDuplicateFindTaclet(app, pos, goal);
    }

    @Override
    protected boolean comparePio(TacletApp newApp, TacletApp oldApp, PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        final Term newFocus = newPio.subTerm();
        final Term oldFocus = oldPio.subTerm();
        if (!newFocus.equalsModIrrelevantTermLabels(oldFocus)) {
            return false;
        }

        if (newFocus.isRigid()) {
            return true;
        }

        final ImmutableList<UpdateLabelPair> oldUpdateContext =
            oldApp.instantiations().getUpdateContext();
        final ImmutableList<UpdateLabelPair> newUpdateContext =
            newApp.instantiations().getUpdateContext();
        return oldUpdateContext.equals(newUpdateContext);
    }
}
