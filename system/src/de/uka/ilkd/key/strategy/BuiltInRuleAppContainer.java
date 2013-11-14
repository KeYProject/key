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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.FormulaTag;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.*;


/**
 * Instances of this class are immutable
 */
public class BuiltInRuleAppContainer extends RuleAppContainer {

    /**
     * The position of the rule app in two different representations:
     * <code>positionTag</code> denotes the concerned formula and survives
     * modifications of the sequent and of parts of the formula, and
     * <code>applicationPosition</code> is the original position for which the
     * rule app was created
     */
    private final FormulaTag      positionTag;
    private final PosInOccurrence applicationPosition;
    
    private final IBuiltInRuleApp bir;
    
    

    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------
        
    private BuiltInRuleAppContainer(IBuiltInRuleApp bir,
			     	    PosInOccurrence pio,
			     	    RuleAppCost     cost,
			     	    Goal            goal) {
        super(bir, cost);
    	applicationPosition = pio;
    	positionTag 
    		= pio == null 
    	          ? null 
    	          : goal.getFormulaTagManager().getTagForPos(pio.topLevel());
        this.bir = bir;
    	assert !(pio != null && positionTag == null) 
    	       : "Formula " + pio + " does not exist";
    }
    
    
    

    //-------------------------------------------------------------------------
    //internal methods
    //-------------------------------------------------------------------------
    
    /**
     * @return true iff the stored rule app is applicable for the given sequent,
     * i.e. if the bound position does still exist (if-formulas are not
     * considered)
     */
    private boolean isStillApplicable(Goal goal) {
	if(applicationPosition == null) {
	    return bir.rule().isApplicable(goal,  null);	    
	} else {
            final PosInOccurrence topPos 
    		= goal.getFormulaTagManager().getPosForTag(positionTag);
            if(topPos == null) {
        	//the formula does not exist anymore, bail out
        	return false;
            } else if(topPos.constrainedFormula()
        	            .equals(applicationPosition.constrainedFormula())) {
        	return true;
            } else {
        	return false;
            }
	}
    }
    
    
    /**
     * Copied from FindTaclet.
     */
    private PosInOccurrence getPosInOccurrence(Goal p_goal) {
    	final PosInOccurrence topPos =
    	    p_goal.getFormulaTagManager().getPosForTag(positionTag);

	assert topPos != null;
	
	return applicationPosition.replaceConstrainedFormula
	    ( topPos.constrainedFormula () );
    }    
    
    

    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------
    
    /**
     * Create containers for RuleApps.
     * @return list of containers for currently applicable BuiltInRuleApps,
     * the cost may be an instance of <code>TopRuleAppCost</code>.
     */
    static ImmutableList<RuleAppContainer> createAppContainers( 
	    					IBuiltInRuleApp bir,
	    					PosInOccurrence pio,
	    					Goal goal,
	    					Strategy strategy ) {
        final RuleAppCost cost = strategy.computeCost(bir, pio, goal);

        final BuiltInRuleAppContainer container 
        	= new BuiltInRuleAppContainer(bir, pio, cost, goal);

        return ImmutableSLList.<RuleAppContainer>nil().prepend(container);
    }    
    

    @Override
    public ImmutableList<RuleAppContainer> createFurtherApps(
	    					Goal goal,
	    					Strategy strategy) {
        if(!isStillApplicable(goal)) {
            return ImmutableSLList.<RuleAppContainer>nil();
        }
        
        final PosInOccurrence pio = getPosInOccurrence(goal);
        
        ImmutableList<RuleAppContainer> result 
        	= createAppContainers(bir, pio, goal, strategy);
        for(RuleAppContainer container : result) {
            if(container.getCost() instanceof TopRuleAppCost) {
        	result = result.removeFirst(container);
            }
        }
        return result;
    }
    

    @Override
    public RuleApp completeRuleApp(Goal goal, Strategy strategy) {
        if(!isStillApplicable(goal)) {
            return null;
        }
        
        final PosInOccurrence pio = getPosInOccurrence (goal);
        if(!strategy.isApprovedApp(bir, pio, goal)) {
            return null;
        }                
        
        final BuiltInRule rule = bir.rule();
        IBuiltInRuleApp app = rule.createApp(pio);
		
		if (!app.complete()) {
		    app = app.setIfInsts(bir.ifInsts());
		    // TODO: check for force ?
		    final boolean force = true;
			app = force? app.forceInstantiate(goal): app.tryToInstantiate(goal);
		}

		return app.complete() ? app : null;
    }
}
