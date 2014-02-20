// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
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
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;

/**
 * Feature that returns the number of branches for a given taclet application
 * Size of "assumes" sequents is currently not considered
 */
public class CountBranchFeature implements Feature {
    
    public static Feature INSTANCE = new CountBranchFeature();

    private CountBranchFeature() {
    }

    /**
     * Compute the cost of a RuleApp.
     * @param app the RuleApp
     * @param pos position where <code>app</code> is to be applied
     * @param goal the goal on which <code>app</code> is to be applied
     * @return the cost of <code>app</code>
     */
    public RuleAppCost compute ( RuleApp app, PosInOccurrence pos, Goal goal ) {	
	if (app.rule() instanceof Taclet) {
	    final Taclet tac     = (Taclet)app.rule();
	    final long branches  = tac.goalTemplates().size();	    
	    return NumberRuleAppCost.create(branches);
	}
	return NumberRuleAppCost.getZeroCost();
    }
}
