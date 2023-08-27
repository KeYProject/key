/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/**
 * Binary feature that returns zero iff the position of the given rule app is not within the scope
 * of a quantifier
 */
public class NotBelowQuantifierFeature extends BinaryFeature {

    public static final Feature INSTANCE = new NotBelowQuantifierFeature();

    private NotBelowQuantifierFeature() {}

    public boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        Debug.assertFalse(pos == null, "Feature is only applicable to rules with find");

        return !belowQuantifier(pos);
    }

    /**
     * @return true iff the given position is in the scope of a quantifier
     */
    private boolean belowQuantifier(PosInOccurrence pos) {
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final Term t = it.getSubTerm();
            final Operator op = t.op();

            if (op instanceof Quantifier) {
                return true;
            }
        }

        return false;
    }

}
