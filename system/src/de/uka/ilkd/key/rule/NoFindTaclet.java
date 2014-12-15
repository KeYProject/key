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

package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentChangeInfo;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.Taclet.TacletLabelHint.TacletOperation;
import de.uka.ilkd.key.rule.tacletbuilder.NoFindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;

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
     * @param goalTemplates the IList<TacletGoalTemplate> containg all goal descriptions of the taclet to be created
     * @param ruleSets a list of rule sets for the Taclet
     * @param attrs attributes for the Taclet; these are boolean values
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the
     * prefix for each SchemaVariable in the Taclet
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public NoFindTaclet(Name name, TacletApplPart applPart,  
		      ImmutableList<TacletGoalTemplate> goalTemplates, 
		      ImmutableList<RuleSet> ruleSets, 
		      TacletAttributes attrs,
		      ImmutableMap<SchemaVariable,TacletPrefix> prefixMap,
		      ImmutableSet<Choice> choices){
	super(name, applPart, goalTemplates, ruleSets, attrs, prefixMap, 
	      choices);
	cacheMatchInfo();
    } 

   /**
    * adds the sequent of the add part of the Taclet to the goal sequent
    * 
    * @param add
    *           the Sequent to be added
    * @param currentSequent
    *           the Sequent which is the current (intermediate) result of
    *           applying the taclet
    * @param services
    *           the Services encapsulating all java information
    * @param matchCond
    *           the MatchConditions with all required instantiations
    */   
   protected void applyAdd(Sequent add,
         SequentChangeInfo currentSequent, Services services,
         MatchConditions matchCond) {
      addToAntec(add.antecedent(), currentSequent, null, services, matchCond, null, new TacletLabelHint(TacletOperation.ADD_ANTECEDENT, add));
      addToSucc(add.succedent(), currentSequent, null, services, matchCond, null, new TacletLabelHint(TacletOperation.ADD_SUCCEDENT, add));
   }    

    /**
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed
     */
    public ImmutableList<Goal> apply(Goal     goal,
			    Services services, 
			    RuleApp  ruleApp) {

	// Number without the if-goal eventually needed
	int                          numberOfNewGoals = goalTemplates().size();

	TacletApp                    tacletApp        = (TacletApp) ruleApp;
	MatchConditions              mc               = tacletApp.matchConditions ();

	ImmutableList<SequentChangeInfo> newSequentsForGoals         =
	    checkIfGoals ( goal,
			   tacletApp.ifFormulaInstantiations (),
			   mc,
			   numberOfNewGoals );
	
	ImmutableList<Goal> newGoals = goal.split(newSequentsForGoals.size());
   
   Iterator<TacletGoalTemplate> it               = goalTemplates().iterator();
   Iterator<Goal>               goalIt           = newGoals.iterator();
   Iterator<SequentChangeInfo> newSequentsIt     = newSequentsForGoals.iterator();	

	while (it.hasNext()) {
	    TacletGoalTemplate gt          = it    .next();
	    Goal               currentGoal = goalIt.next();
	    // add first because we want to use pos information that
	    // is lost applying replacewith
	    
	    SequentChangeInfo currentSequent = newSequentsIt.next();
	    
	    applyAdd(   gt.sequent(),
	                currentSequent,
	                services,
	                mc);
	    
	    applyAddrule(     gt.rules(),
			      currentGoal,
			      services,
			      mc);

	    applyAddProgVars( gt.addedProgVars(),
	          currentSequent,  
	          currentGoal,
	          tacletApp.posInOccurrence(),
	          services,
			      mc);

       currentGoal.setSequent(currentSequent);

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
    public ImmutableSet<SchemaVariable> getIfFindVariables () {
	return getIfVariables ();
    }

    /**
     * the empty set as a no find taclet has no other entities where 
     * variables cann occur bound than in the goal templates
     * @return empty set
     */
    protected ImmutableSet<QuantifiableVariable> getBoundVariablesHelper() {        
        return DefaultImmutableSet.<QuantifiableVariable>nil();
    }

}