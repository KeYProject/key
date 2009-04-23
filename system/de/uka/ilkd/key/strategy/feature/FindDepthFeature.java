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
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;


/**
 * A feature that computes the depth of the find-position of a taclet (top-level
 * positions have depth zero) 
 * 
 * TODO: eliminate this class and use term features instead
 */
public class FindDepthFeature implements Feature {

    public static final Feature INSTANCE = new FindDepthFeature ();

    private FindDepthFeature () {}
    
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        assert pos != null : "Feature is only applicable to rules with find";

        return LongRuleAppCost.create ( pos.depth () );
    }

}
