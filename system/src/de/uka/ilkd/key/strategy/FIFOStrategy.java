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


package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * Trivial implementation of the Strategy interface
 * that uses only the goal time to determine the cost
 * of a RuleApp.
 */
public class FIFOStrategy implements Strategy {
    
    private static final Name NAME = new Name ( "FIFO" );

    private FIFOStrategy () {
    }

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     * @return the cost of the rule application expressed as
     * a <code>RuleAppCost</code> object.
     * <code>TopRuleAppCost.INSTANCE</code> indicates
     * that the rule shall not be applied at all 
     * (it is discarded by the strategy).
     */
    public RuleAppCost computeCost ( RuleApp         app,
	                             PosInOccurrence pio,
	                             Goal            goal ) {
	return LongRuleAppCost.create ( goal.getTime () );
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is
     * called immediately before a rule is really applied
     * @return true iff the rule should be applied, false otherwise
     */
    public boolean isApprovedApp (  RuleApp         app,
	                            PosInOccurrence pio,
	                            Goal            goal ) {
	return true;
    }

    public void instantiateApp(RuleApp app,
                               PosInOccurrence pio,
                               Goal goal,
                               RuleAppCostCollector collector) {}

    public Name name () {
        return NAME;
    }
    
    public static Strategy INSTANCE = new FIFOStrategy ();
    
    public static class Factory extends StrategyFactory {
        public Name name () {
            return NAME;
        }
        
        public Strategy create ( Proof proof, StrategyProperties properties ) {
            return INSTANCE;
        }
    }

}
