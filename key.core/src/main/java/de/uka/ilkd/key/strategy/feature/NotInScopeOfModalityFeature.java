/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/**
 * Returns zero iff the position of a rule application is not in the scope of a modal operator (a
 * program block or an update). Note that terms and formulas within (but not behind) updates are not
 * in the scope of the update
 */
public class NotInScopeOfModalityFeature extends BinaryFeature {

    public static final Feature INSTANCE = new NotInScopeOfModalityFeature();

    private NotInScopeOfModalityFeature() {}

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        Debug.assertFalse(pos == null, "Feature is only applicable to rules with find");

        return !inScopeOfModality(pos);
    }

    private boolean inScopeOfModality(PosInOccurrence pos) {
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final Operator op = it.getSubTerm().op();

            if (op instanceof Modality) {
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
