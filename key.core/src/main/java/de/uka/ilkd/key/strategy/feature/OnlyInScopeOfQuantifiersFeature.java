/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;


/**
 * BinaryFeature that return zero if all the operator is quantifier from root to position it point
 * to.
 */
public class OnlyInScopeOfQuantifiersFeature extends BinaryTacletAppFeature {

    public final static Feature INSTANCE = new OnlyInScopeOfQuantifiersFeature();

    private OnlyInScopeOfQuantifiersFeature() {}

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        assert pos != null : "Feature is only applicable to rules with find";

        final PIOPathIterator it = pos.iterator();
        while (it.next() != -1) {
            final Term subterm = it.getSubTerm();
            if (!(subterm.op() instanceof Quantifier)) {
                return false;
            }
        }

        return true;
    }
}
