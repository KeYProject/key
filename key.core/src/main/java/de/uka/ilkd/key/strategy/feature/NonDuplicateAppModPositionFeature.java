/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.util.collection.ImmutableList;

import static de.uka.ilkd.key.logic.equality.IrrelevantTermLabelsProperty.IRRELEVANT_TERM_LABELS_PROPERTY;

/**
 * Binary feature that returns zero iff a certain Taclet app has not already been performed
 */
public class NonDuplicateAppModPositionFeature extends NonDuplicateAppFeature {

    public static final Feature INSTANCE = new NonDuplicateAppModPositionFeature();

    @Override
    protected boolean comparePio(TacletApp newApp, TacletApp oldApp,
            PosInOccurrence newPio,
            PosInOccurrence oldPio) {
        final JTerm newFocus = (JTerm) newPio.subTerm();
        final JTerm oldFocus = (JTerm) oldPio.subTerm();
        if (!newFocus.equalsModProperty(oldFocus, IRRELEVANT_TERM_LABELS_PROPERTY)) {
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
