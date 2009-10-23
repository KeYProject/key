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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.BuiltInRuleApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;


public final class BuiltInNonDuplicateAppModPositionFeature 
						extends BinaryFeature {
    
    public static final BuiltInNonDuplicateAppModPositionFeature INSTANCE
    	= new BuiltInNonDuplicateAppModPositionFeature();
    
    private BuiltInNonDuplicateAppModPositionFeature() {}
    
    
    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
	final BuiltInRuleApp bapp = (BuiltInRuleApp) app; 
	final BuiltInRule rule = bapp.rule();
	final Term term = pos.subTerm();
	final ImmutableList<PosInOccurrence> ifInsts = bapp.ifInstantiations();
		
//if(node.serialNr() == 433 || node.serialNr() == 421) {
//    myNode = true;
//    System.out.println("Checking for " + node.serialNr());
//    System.out.println("###Term: ");
//    System.out.println(term);
//    if(lastTerm != null) {
//	System.out.println("###Last term: ");
//	System.out.println(lastTerm);
//	System.out.println("###Equal: "  + lastTerm.equals(term));
//    }
//    lastTerm = term;
//}
	
	Node node = goal.node();	
	while(!node.root()) {
	    node = node.parent();
	    RuleApp app2 = node.getAppliedRuleApp();
	    if(app2.rule().equals(rule) 
	       && app2.posInOccurrence().subTerm().equals(term)) {
		return false;
	    }
	}
	return true;
    }
}
