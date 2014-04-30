// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Feature that computes the age of the goal (i.e. total number of rules
 * applications that have been performed at the goal) to which a rule is
 * supposed to be applied
 */
public class AgeFeature implements Feature {
    
    public static final Feature INSTANCE = new AgeFeature ();

    private AgeFeature () {}
    
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {
        return NumberRuleAppCost.create ( goal.getTime() );
//        return LongRuleAppCost.create ( goal.getTime() / goal.sequent ().size () );
//        return LongRuleAppCost.create ( (long)Math.sqrt ( goal.getTime () ) );
    }

}