/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.JTerm;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.BinaryFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;


/**
 * Binary feature that returns zero iff the find-formula of a rule contains a d-path consisting only
 * of positive literals (as a formula of the antecedent). Used terminology is defined in Diss. by
 * Martin Giese.
 */
public class PurePosDPathFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new PurePosDPathFeature();

    private PurePosDPathFeature() {}

    @Override
    protected RuleAppCost doComputation(PosInOccurrence pos, JTerm findTerm, ServiceCaches caches) {
        return hasPurePosPath(findTerm, !pos.isInAntec(), caches) ? BinaryFeature.ZERO_COST
                : BinaryFeature.TOP_COST;
    }

}
