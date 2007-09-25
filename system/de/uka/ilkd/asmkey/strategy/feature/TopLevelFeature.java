// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.feature.Feature;


/**
 * A feature that computes the depth of the find-position of a taclet (top-level
 * positions have depth zero) 
 */
public class TopLevelFeature implements Feature {

    public static Feature createTopLevel(RuleAppCost cost) {
	return new TopLevelFeature (cost);
    }

    public static Feature createTopLevel(long cost) {
	return createTopLevel(LongRuleAppCost.create(cost));
    }

    private final RuleAppCost cost;

    private TopLevelFeature(RuleAppCost cost) {
	this.cost = cost;
    }
	 
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        assert pos != null : "Feature is only applicable to rules with find";

        if (pos.depth() == 0) {
	    return LongRuleAppCost.ZERO_COST;
	} else {
	    return cost;
	}
    }

}
