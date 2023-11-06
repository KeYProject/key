/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;


/**
 * Feature that returns zero iff the application focus of a rule is a potential cut position (taclet
 * cut_direct). For positions that are below quantifiers, the feature generally returns zero.
 */
public class AllowedCutPositionFeature extends BinaryFeature {

    public static final Feature INSTANCE = new AllowedCutPositionFeature();

    private AllowedCutPositionFeature() {}

    public boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
        Debug.assertFalse(pos == null, "Feature is only applicable to rules with find");

        return onlyBelowRightJunctors(pos);
    }

    private boolean onlyBelowRightJunctors(PosInOccurrence pos) {
        boolean negated = pos.isInAntec();
        final PIOPathIterator it = pos.iterator();

        while (it.next() != -1) {
            final int child = it.getChild();
            final Operator op = it.getSubTerm().op();

            if (op == Junctor.NOT) {
                negated = !negated;
            } else if (op == (negated ? Junctor.OR : Junctor.AND)) {
                /* nothing */
            } else if (negated && op == Junctor.IMP) {
                if (child == 0) {
                    negated = !negated;
                }
            } else {
                return op instanceof Quantifier;
            }
        }

        return true;
    }

}
