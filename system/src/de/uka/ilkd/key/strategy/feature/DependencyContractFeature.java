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

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.speclang.HeapContext;


public final class DependencyContractFeature extends BinaryFeature {
    
        
    private void removePreviouslyUsedSteps(
	    			Term focus, 
	    			Goal goal,
	    			List<PosInOccurrence> steps) {
	Node node = goal.node();
	while(!node.root()) {
	    node = node.parent();
	    final RuleApp app = node.getAppliedRuleApp();
	    if(app.rule() instanceof UseDependencyContractRule
	       && app.posInOccurrence().subTerm().equals(focus)) {
		final IBuiltInRuleApp bapp = (IBuiltInRuleApp) app;
		for(PosInOccurrence ifInst : bapp.ifInsts()) {
		    steps.remove(ifInst);
		}
	    }
	}
    }
    
    
    
    @Override
    protected boolean filter(RuleApp app,
	    		     PosInOccurrence pos,
	    		     Goal goal) {
	IBuiltInRuleApp bapp = (IBuiltInRuleApp) app; 
	final Term focus = pos.subTerm();

	//determine possible steps
	
	List<LocationVariable> heapContext =
	     bapp.getHeapContext() != null ? bapp.getHeapContext() :
		 HeapContext.getModHeaps(goal.proof().getServices(), false);

	final List<PosInOccurrence> steps 
		= UseDependencyContractRule.getSteps(heapContext, pos, 
				goal.sequent(), 
				goal.proof().getServices());
	if(steps.isEmpty()) {
	    return false;
	}
	
	//remove previously used steps
	removePreviouslyUsedSteps(focus, goal, steps);
	if(steps.isEmpty()) {
	    return false;
	}
	
	//instantiate with arbitrary remaining step
	bapp = bapp.setIfInsts(ImmutableSLList.<PosInOccurrence>nil()
		        .prepend(steps.get(0)));
	return true;
    }
}