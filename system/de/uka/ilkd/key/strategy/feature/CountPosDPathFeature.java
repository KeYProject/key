// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * Feature that returns the maximum number of positive literals occurring within
 * a d-path of the find-formula as a formula of the antecedent. Used terminology
 * is defined in Diss. by Martin Giese.
 */
public class CountPosDPathFeature extends AbstractBetaFeature {

    public final static Feature INSTANCE = new CountPosDPathFeature ();

    private CountPosDPathFeature () {}

    protected RuleAppCost doComputation (PosInOccurrence pos, Term findTerm) {
        return LongRuleAppCost.create ( maxPosPath ( findTerm, !pos.isInAntec () ) );
    }

}
