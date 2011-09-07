// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;

/** 
 * this class represents an application of a built in rule
 * application
 */
public class BuiltInRuleApp implements RuleApp {
   
    private BuiltInRule builtInRule;
    private PosInOccurrence pio;
    private ImmutableList<PosInOccurrence> ifInsts 
    	= ImmutableSLList.nil();

   
    public BuiltInRuleApp(BuiltInRule builtInRule, 
			  PosInOccurrence pio) {
	this.builtInRule    = builtInRule;
	this.pio            = pio;
    }
    
    
    public BuiltInRuleApp(BuiltInRule builtInRule, 
			  PosInOccurrence pio,
			  ImmutableList<PosInOccurrence> ifInsts) {
	this(builtInRule, pio);
	this.ifInsts = ifInsts;
    }
    

    /**
     * returns the rule of this rule application
     */
    @Override
    public BuiltInRule rule() {
	return builtInRule;
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and
     * a position in the corresponding formula) of this rule application
     */
    @Override
    public PosInOccurrence posInOccurrence() {
	return pio;
    }

    /** applies the specified rule at the specified position 
     * if all schema variables have been instantiated
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals 
     */
    @Override    
    public ImmutableList<Goal> execute(Goal goal, Services services) {
	goal.addAppliedRuleApp(this);
	ImmutableList<Goal> result = null;
	try {
	    result = builtInRule.apply(goal, services, this);
	} catch (RuleAbortException e) {
	    result = null;
	} catch (Exception e) {
	    result = null;
    }
	if (result == null)
	    goal.removeAppliedRuleApp();
	return result;
    }
    
    public void setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
	assert ifInsts != null;
	this.ifInsts = ifInsts;
    }
    
    
    public ImmutableList<PosInOccurrence> ifInsts() {
	return ifInsts;
    }
    

    /** returns true if all variables are instantiated 
     * @return true if all variables are instantiated 
     */
    @Override    
    public boolean complete() {
	return true;
    }
    
    @Override    
    public String toString() {
	return "BuiltInRule: " + rule().name() + " at pos " + pio.subTerm();
    }
}
