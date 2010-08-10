// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/** 
 * this class represents an application of a built in rule
 * application
 */
public class BuiltInRuleApp implements RuleApp {
   
    private BuiltInRule builtInRule;
    private PosInOccurrence pio;
    private Constraint userConstraint;

    
    /** 
     * 
     */
    public BuiltInRuleApp(BuiltInRule builtInRule, 
			  PosInOccurrence pio,
			  Constraint userConstraint) {
	this.builtInRule    = builtInRule;
	this.pio            = pio;
	this.userConstraint = userConstraint;        
    }

    /**
     * returns the rule of this rule application
     */
    public Rule rule() {
	return builtInRule;
    }

    /**
     * returns the PositionInOccurrence (representing a ConstrainedFormula and
     * a position in the corresponding formula) of this rule application
     */
    public PosInOccurrence posInOccurrence() {
	return pio;
    }

    /** applies the specified rule at the specified position 
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals 
     */
    public ImmutableList<Goal> execute(Goal goal, Services services) {
	goal.addAppliedRuleApp(this);	
	ImmutableList<Goal> result = builtInRule.apply(goal, services, this);
	if (result == null)
	    goal.removeAppliedRuleApp();
	return result;
    }

    /**
     * returns the constraint under which a rule is applicable
     */
    public Constraint constraint () {
	return Constraint.BOTTOM;
    }

    /**
     * returns the user constraint
     */
    public Constraint userConstraint () {
	return userConstraint;
    }

    /** returns true if all variables are instantiated 
     * @return true if all variables are instantiated 
     */
    public boolean complete() {
	return true;
    }
    
    /**
     * toString
     */
    public String toString() {
	return ""+rule().name();
    }

}
