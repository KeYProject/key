/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Feature that returns zero if there is no atom with negative polarity on a common d-path and on
 * the left of the find-position within the find-formula as a formula of the antecedent. Used
 * terminology is defined in Diss. by Martin Giese.
 */
public class LeftmostNegAtomFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new LeftmostNegAtomFeature();

    private LeftmostNegAtomFeature() {}

    @Override
    protected RuleAppCost doComputation(PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        final PIOPathIterator it = pos.iterator();
        boolean positive = pos.isInAntec();

        while (it.next() != -1) {
            final Term subTerm = it.getSubTerm();
            final Operator op = subTerm.op();

            if (it.getChild() == 0) {
                if (op == Junctor.NOT || op == Junctor.IMP) {
                    positive = !positive;
                } else if (op == Equality.EQV) {
                    return BinaryFeature.ZERO_COST; // TODO
                }

                continue;
            }

            if (op == (positive ? Junctor.OR : Junctor.AND)) {
                if (containsNegAtom(subTerm.sub(0), positive, caches)) {
                    return BinaryFeature.TOP_COST;
                }
            } else if (positive && op == Junctor.IMP) {
                if (containsNegAtom(subTerm.sub(0), false, caches)) {
                    return BinaryFeature.TOP_COST;
                }
            } else if (op == Equality.EQV) {
                return BinaryFeature.ZERO_COST; // TODO
            }
        }

        return BinaryFeature.ZERO_COST;
    }

}
