// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.util.Debug;

/**
 * Container for RuleApp instances with cost as determined by 
 * a given Strategy.
 * Instances of this class are immutable
 */
public abstract class RuleAppContainer implements Comparable<RuleAppContainer> {

    /**
     * The stored rule app
     */
    private final RuleApp     ruleApp;

    /**
     * The costs of the stored rule app
     */
    private final RuleAppCost cost;

    protected RuleAppContainer ( RuleApp         p_app,
				 RuleAppCost     p_cost ) {
	ruleApp = p_app;
    	cost    = p_cost;
    }

    public int compareTo(RuleAppContainer o) {
	return cost.compareTo ( o.cost );
    }

    /**
     * Create a list of new RuleAppContainers that are to be 
     * considered for application.
     */
    public abstract ListOfRuleAppContainer createFurtherApps
	( Goal p_goal, Strategy strategy );

    /**
     * Create a <code>RuleApp</code> that is suitable to be applied 
     * or <code>null</code>.
     */
    public abstract RuleApp completeRuleApp ( Goal p_goal, Strategy strategy );

    protected RuleApp getRuleApp () {
	return ruleApp;
    }


    public RuleAppCost getCost () {
    	return cost;
    }


    /**
     * Create containers for RuleApps.
     * @return list of containers for currently applicable RuleApps, the cost
     * may be an instance of <code>TopRuleAppCost</code>.
     */
    public static ListOfRuleAppContainer createAppContainers
        ( RuleApp p_app, PosInOccurrence p_pio, Goal p_goal, Strategy p_strategy ) {

	if ( p_app instanceof NoPosTacletApp )
	    return TacletAppContainer.createAppContainers
		( (NoPosTacletApp)p_app, p_pio, p_goal, p_strategy );

	if ( p_app instanceof BuiltInRuleApp )
	    return BuiltInRuleAppContainer.createAppContainers
		( (BuiltInRuleApp)p_app, p_pio, p_goal, p_strategy );

	Debug.fail ( "Unexpected kind of rule." );

	return null;
    }

}
