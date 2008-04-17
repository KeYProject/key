// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.soundness;

import org.apache.log4j.Logger;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.ListOfGoal;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.rule.*;

/**
 * This class is actually not used; taclet po are created through the methods of
 * proof.init
 */
public class TacletPORule implements BuiltInRule {

    private final Name name = new Name("Create Taclet PO");

    public TacletPORule() {      
    }

    /**
     * returns true iff a rule is applicable at the given
     * position. This does not necessary mean that a rule application
     * will change the goal (this decision is made due to performance
     * reasons)
     */
    public boolean isApplicable(Goal            goal, 				
				PosInOccurrence pio,
				Constraint      userConstraint) {
	if (pio == null) {
	    return true;
	}
	return false;
    }

    public ListOfGoal apply(Goal     goal, 
			    Services services, 
			    RuleApp  ruleApp) {
        final Logger logger = Logger.getLogger ( "key.taclet_soundness" );

        final TacletIndex tacletIndex =
	    goal.ruleAppIndex ().tacletIndex ();

	POSelectionDialog dialog = new POSelectionDialog 
	    (Main.hasInstance() ? Main.getInstance().mediator().mainFrame() : null,
	     tacletIndex.allNoPosTacletApps());
			    	
    	NoPosTacletApp app = dialog.getSelectedTaclets()[0]; 
    	           //TODO: Extend for more than one taclet

	// TODO: well, we have to find a better way to cope with null 
        
        logger.debug ( "Selected taclet: " + app );

	//	StaticChecker sc = new StaticChecker ( services );
	//	sc.visit ( app.taclet (), false );


	POBuilder pob = new POBuilder ( app, services );
	pob.build ();

	ListOfGoal newGoals = goal.split ( 1 );

	newGoals.head ().addFormula
	    ( new ConstrainedFormula ( pob.getPOTerm (), Constraint.BOTTOM ),
	      false, false );

	updateNamespaces ( newGoals.head (), pob );

        logger.debug ( "Resulting PO: " + app );

	return newGoals;
    }


    private void updateNamespaces ( Goal      p_goal,
				    POBuilder p_pob ) {
	NamespaceSet globalNss = p_goal.proof ().getNamespaces ();
	Namespace    funcNs    = globalNss.functions ();

	{
	    IteratorOfNamed it =
		p_pob.getFunctions ().allElements ().iterator ();
	    while ( it.hasNext () )
		funcNs.add ( it.next () );
	}

	{
	    IteratorOfTacletApp it = p_pob.getTaclets ().iterator ();
	    TacletApp           app;
	    while ( it.hasNext () ) {
		app = it.next ();
		p_goal.addTaclet ( app.taclet         (),
				   app.instantiations (),
				   app.constraint     (),
                                   false);
	    }
	}
    }


    public Name name() {
	return name;
    }

    public String displayName() {
	return name().toString();
    }
    
    public String toString() {
	return name().toString();
    }       
}
