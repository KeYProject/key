/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Feature that returns the maximum number of positive literals occurring within a d-path of the
 * find-formula as a formula of the antecedent. Used terminology is defined in Diss. by Martin
 * Giese.
 */
public class CountPosDPathFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new CountPosDPathFeature();

    private CountPosDPathFeature() {}

    @Override
    protected RuleAppCost doComputation(PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return NumberRuleAppCost.create(maxPosPath(findTerm, !pos.isInAntec(), caches));
    }

}
