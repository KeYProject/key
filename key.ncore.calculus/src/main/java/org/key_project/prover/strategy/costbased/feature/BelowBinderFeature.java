/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;

import org.jspecify.annotations.NonNull;


/**
 * Returns zero iff the position of a rule application is not below any operators that bind
 * variables
 */
public class BelowBinderFeature<Goal extends ProofGoal<@NonNull Goal>> extends BinaryFeature<Goal> {

    private static final Feature<?> INSTANCE = new BelowBinderFeature<>();

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature<Goal> getInstance() {
        // noinspection unchecked
        return (Feature<Goal>) INSTANCE;
    }

    private BelowBinderFeature() {}

    public boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        return belowBinder(pos);
    }

    private boolean belowBinder(PosInOccurrence pos) {
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final Term t = it.getSubTerm();

            if (!t.varsBoundHere(it.getChild()).isEmpty()) {
                return true;
            }
        }

        return false;
    }

}
