/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Binary feature that returns zero iff the hyper-tableaux simplification method approves the given
 * application (which is supposed to be the application of a beta rule). Used terminology is defined
 * in Diss. by Martin Giese.
 */
public class SimplifyBetaCandidateFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new SimplifyBetaCandidateFeature();

    private SimplifyBetaCandidateFeature() {}

    @Override
    protected RuleAppCost doComputation(PosInOccurrence pos, Term findTerm, ServiceCaches caches) {
        return isBetaCandidate(findTerm, pos.isInAntec(), caches) ? BinaryFeature.ZERO_COST
                : BinaryFeature.TOP_COST;
    }

}
