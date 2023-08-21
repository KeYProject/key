/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Binary feature that returns zero iff the focus of a rule contains a quantifier
 *
 * NB: this can nowadays be done more nicely using term features
 */
public class ContainsQuantifierFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new ContainsQuantifierFeature();

    private ContainsQuantifierFeature() {}

    @Override
    protected RuleAppCost doComputation(PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return containsQuantifier(findTerm, caches) ? BinaryFeature.ZERO_COST
                : BinaryFeature.TOP_COST;
    }

}
