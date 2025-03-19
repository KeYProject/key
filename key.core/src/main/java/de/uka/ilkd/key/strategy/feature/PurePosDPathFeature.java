/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Binary feature that returns zero iff the find-formula of a rule contains a d-path consisting only
 * of positive literals (as a formula of the antecedent). Used terminology is defined in Diss. by
 * Martin Giese.
 */
public class PurePosDPathFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new PurePosDPathFeature();

    private PurePosDPathFeature() {}

    @Override
    protected RuleAppCost doComputation(PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return hasPurePosPath(findTerm, !pos.isInAntec(), caches) ? BinaryFeature.ZERO_COST
                : BinaryFeature.TOP_COST;
    }

}
