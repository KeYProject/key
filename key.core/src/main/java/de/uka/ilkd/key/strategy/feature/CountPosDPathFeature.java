/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.Term;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;


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
