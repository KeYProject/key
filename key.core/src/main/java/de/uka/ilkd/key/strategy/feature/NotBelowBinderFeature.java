/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;


/**
 * Returns zero iff the position of a rule application is not below any operators that bind
 * variables
 */
public class NotBelowBinderFeature extends BinaryFeature {

    public static final Feature<Goal> INSTANCE = new NotBelowBinderFeature();

    private NotBelowBinderFeature() {}

    public boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        return !belowBinder(pos);
    }

    private boolean belowBinder(PosInOccurrence pos) {
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final Term t = (Term) it.getSubTerm();

            if (!t.varsBoundHere(it.getChild()).isEmpty()) {
                return true;
            }
        }

        return false;
    }

}
