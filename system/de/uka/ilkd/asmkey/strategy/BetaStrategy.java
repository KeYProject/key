// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.Feature;

/**
 * Simple strategy to use beta rules automatically.
 */
public class BetaStrategy extends AbstractFeatureStrategy {

    private static final Name NAME = new Name("BetaStrategy");

    private Feature betaF;

    protected BetaStrategy(Proof p) {
	super (p);

	betaF = ifHeuristics( new String[] { "beta" },
			      longConst(0),
			      inftyConst());

    }

    public Name name() {
	return NAME;
    }

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     * 
     * @return the cost of the rule application expressed as a
     *         <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule
     *         shall not be applied at all (it is discarded by the strategy).
     */
    public RuleAppCost computeCost (RuleApp app, PosInOccurrence pio, Goal goal) {
        return betaF.compute ( app, pio, goal );
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is
     * called immediately before a rule is really applied
     * @return true iff the rule should be applied, false otherwise
     */
    public boolean isApprovedApp (RuleApp app, PosInOccurrence pio, Goal goal) {
        return !( betaF.compute ( app, pio, goal ) instanceof TopRuleAppCost );
    }

    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return TopRuleAppCost.INSTANCE;
    }    

    public static class Factory extends StrategyFactory {
	public Strategy create( Proof p, StrategyProperties properties ) {
	    return new BetaStrategy(p);
	}

	public Name name() {
	    return NAME;
	}
    }


}
