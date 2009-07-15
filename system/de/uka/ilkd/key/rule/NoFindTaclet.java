// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.IteratorOfGoal;
import de.uka.ilkd.key.proof.ListOfGoal;

/** 
 * Used to implement a Taclet that has no <I>find</I> part. This kind of taclet
 * is not attached to term or formula, but to a complete sequent. A typical
 * representant is the <code>cut</code> rule. 
 */
public class NoFindTaclet extends Taclet {

    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters.  
     * @param name the name of the Taclet 
     * @param applPart contains the application part of an Taclet that is
     * the if-sequent, the variable conditions
     * @param goalTemplates the ListOfTacletGoalTemplate containg all goal descriptions of the taclet to be created
     * @param ruleSets a list of rule sets for the Taclet
     * @param constraint the Constraint under which the Taclet is valid
     * @param attrs attributes for the Taclet; these are boolean values
     * @param prefixMap a MapFromSchemaVariableToTacletPrefix that contains the
     * prefix for each SchemaVariable in the Taclet
     * @param choices the SetOfChoices to which this taclet belongs to
     */
    public NoFindTaclet(Name name, TacletApplPart applPart,  
		      ListOfTacletGoalTemplate goalTemplates, 
		      ListOfRuleSet ruleSets, 
		      Constraint constraint,
		      TacletAttributes attrs,
		      MapFromSchemaVariableToTacletPrefix prefixMap,
		      SetOfChoice choices){
	super(name, applPart, goalTemplates, ruleSets, constraint, attrs, 
	      prefixMap, choices);
	cacheMatchInfo();
    } 

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param add the Sequent to be added
     * @param goal the Goal to be updated
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected void applyAdd(Sequent add, Goal goal, 
			    Services services,
			    MatchConditions matchCond) {
	addToAntec(add.antecedent(), goal, null, services, matchCond);
	addToSucc (add.succedent(),  goal, null, services, matchCond);
    }
    

    /**
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed
     */
    public ListOfGoal apply(Goal     goal,
			    Services services, 
			    RuleApp  ruleApp) {

	// Number without the if-goal eventually needed
	int                          numberOfNewGoals = goalTemplates().size();

	TacletApp                    tacletApp        = (TacletApp) ruleApp;
	MatchConditions              mc               = tacletApp.matchConditions ();

	// Restrict introduced metavariables to the subtree
	setRestrictedMetavariables ( goal, mc );

	ListOfGoal                   newGoals         =
	    checkIfGoals ( goal,
			   tacletApp.ifFormulaInstantiations (),
			   mc,
			   numberOfNewGoals );
	
	IteratorOfTacletGoalTemplate it               = goalTemplates().iterator();
	IteratorOfGoal               goalIt           = newGoals.iterator();

	while (it.hasNext()) {
	    TacletGoalTemplate gt          = it    .next();
	    Goal               currentGoal = goalIt.next();
	    // add first because we want to use pos information that
	    // is lost applying replacewith
	    applyAdd(         gt.sequent(),
			      currentGoal,
			      services,
			      mc);

	    applyAddrule(     gt.rules(),
			      currentGoal,
			      services,
			      mc);

	    applyAddProgVars( gt.addedProgVars(),
			      currentGoal,
                              tacletApp.posInOccurrence(),
                              services,
			      mc);
                              
            currentGoal.setBranchLabel(gt.name());
	}

	return newGoals;
    }

    protected Taclet setName(String s) {
	NoFindTacletBuilder b=new NoFindTacletBuilder();
	return super.setName(s, b);
    }

    /**
     * @return Set of schemavariables of the if and the (optional)
     * find part
     */
    public SetOfSchemaVariable getIfFindVariables () {
	return getIfVariables ();
    }

    /**
     * the empty set as a no find taclet has no other entities where 
     * variables cann occur bound than in the goal templates
     * @return empty set
     */
    protected SetOfQuantifiableVariable getBoundVariablesHelper() {        
        return SetAsListOfQuantifiableVariable.EMPTY_SET;
    }

}
