/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.UpdateApplication;

import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PIOPathIterator;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;


/**
 * Returns zero iff the position of a rule application is not in the scope of a modal operator (a
 * program block or an update). Note that terms and formulas within (but not behind) updates are not
 * in the scope of the update
 */
public class NotInScopeOfModalityFeature extends BinaryFeature {

    public static final Feature INSTANCE = new NotInScopeOfModalityFeature();

    private NotInScopeOfModalityFeature() {}

    @Override
    protected <Goal extends ProofGoal<@NonNull Goal>> boolean filter(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null : "Feature is only applicable to rules with find";

        return !inScopeOfModality(pos);
    }

    private boolean inScopeOfModality(PosInOccurrence pos) {
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final var op = it.getSubTerm().op();

            if (op instanceof JModality) {
                return true;
            }
            if (op instanceof UpdateApplication) {
                if (it.getChild() == UpdateApplication.targetPos()) {
                    return true;
                }
            }
        }

        return false;
    }

}
