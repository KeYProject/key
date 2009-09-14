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

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;


public final class BuiltInNonDuplicateAppModPositionFeature 
						extends BinaryFeature {
    
    public static final BuiltInNonDuplicateAppModPositionFeature INSTANCE
    	= new BuiltInNonDuplicateAppModPositionFeature();
    
    private BuiltInNonDuplicateAppModPositionFeature() {}
    
    
//    Term lastTerm;
    @Override
    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal) {
	final Rule rule = app.rule();
	final Term term = pos.subTerm();
	Node node = goal.node();

	boolean myNode = false;	
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
