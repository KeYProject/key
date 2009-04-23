// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Visitor;
import de.uka.ilkd.key.rule.*;


public abstract class TacletVisitor extends Visitor {

    /** collects all variables in a Semisequent 
     * @param semiseq the Semisequent to visit
     */
    private void visit(Semisequent semiseq) {
	IteratorOfConstrainedFormula it=semiseq.iterator();
	while(it.hasNext()) {
	    it.next().formula().execPostOrder(this);
	}
    }

    /** goes through the given sequent an collects all vars found
     * @param seq the Sequent to visit
     */
    public void visit(Sequent seq) {
	visit(seq.antecedent());
	visit(seq.succedent());
    }

    /** collects all variables in a Taclet
     * @param taclet the Taclet where the variables have to be collected to
     * @param visitAddrules a boolean that contols if the addrule sections are
     * to be ignored (iff false) or if the visitor descends into them (iff true) 
     */
    public void visit(Taclet taclet, boolean visitAddrules) {
	visit(taclet.ifSequent());
	if (taclet instanceof FindTaclet) {
	    (((FindTaclet)taclet).find()).execPostOrder(this);
	}	
	IteratorOfTacletGoalTemplate it = taclet.goalTemplates().iterator();
	while (it.hasNext()) {
	    TacletGoalTemplate gt=it.next();
	    visit(gt.sequent());
	    if (gt instanceof RewriteTacletGoalTemplate) {
		((RewriteTacletGoalTemplate)gt).replaceWith().execPostOrder(this);
	    } else {
		if(gt instanceof AntecSuccTacletGoalTemplate) {
		    visit(((AntecSuccTacletGoalTemplate)gt).replaceWith());
		}
	    }
	    if (visitAddrules) {
		IteratorOfTaclet addruleIt = gt.rules().iterator();
		while (addruleIt.hasNext()) {
		    visit(addruleIt.next(), true);		    
		}
	    }
	}
    }

}
