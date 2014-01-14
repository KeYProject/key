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


package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApplPart;

/** class builds RewriteTaclet objects.*/
public class RewriteTacletBuilder extends FindTacletBuilder{


    /**
     * encodes restrictions on the state where a rewrite taclet is applicable
     * If the value is equal to 
     * <ul> 
     * <li> {@link RewriteTaclet#NONE} no state restrictions are posed</li>
     * <li> {@link RewriteTaclet#SAME_UPDATE_LEVEL} then <code>\assumes</code> 
     * must match on a formula within the same state as <code>\find</code>
     * rsp. <code>\add</code>. For efficiency no modalities are allowed above 
     * the <code>\find</code> position  </li>
     * <li> {@link RewriteTaclet#IN_SEQUENT_STATE} the <code>\find</code> part is 
     * only allowed to match on formulas which are evaulated in the same state as 
     * the sequent</li>
     *</ul>
     */
    private int applicationRestriction;

    public RewriteTacletBuilder setApplicationRestriction
	( int p_applicationRestriction ) {
	applicationRestriction = p_applicationRestriction;
	return this;
    }

    /** sets the <I>find</I> of the Taclet that is to build to the given
     * term.
     * @return this RewriteTacletBuilder
     */ 
    public RewriteTacletBuilder setFind(Term findTerm) {
	checkContainsFreeVarSV(findTerm, this.getName(), "find term");
	find=findTerm;
	return this;
    }

    /** builds and returns the RewriteTaclet that is specified by
     * former set... / add... methods. If no name is specified then
     * an Taclet with an empty string name is build. No specifications
     * for variable conditions, goals or heuristics imply that the
     * corresponding parts of the Taclet are empty. No specification for
     * the if-sequent is represented as a sequent with two empty
     * semisequents. No specification for the interactive or
     * recursive flags imply that the flags are not set. 
     * No specified find part causes an TacletBuilderException.
     * Throws an
     * TacletBuilderException if a bound SchemaVariable occurs more than once in if
     * and find or an InvalidPrefixException if the building of the Taclet 
     * Prefix fails.
     */
    public RewriteTaclet getRewriteTaclet(){
	if (find==null) {
	    throw new TacletBuilderException(this, "No find part specified");
	    
	}
	checkBoundInIfAndFind();
	TacletPrefixBuilder prefixBuilder=new TacletPrefixBuilder(this);
	prefixBuilder.build();
	return new RewriteTaclet(name, 
				 new TacletApplPart(ifseq,
						    varsNew,
						    varsNotFreeIn,
						    varsNewDependingOn,
						    variableConditions),
				 goals, ruleSets,
				 attrs,
				 find,
				 prefixBuilder.getPrefixMap(),
				 applicationRestriction,
				 choices);
    }

    /**
     * adds a new goal descriptions to the goal descriptions of the Taclet.
     * the TacletGoalTemplate must not be an AntecSuccTacletGoalTemplate,
     * otherwise an illegal argument exception is thrown.
     */
    @Override
    public void addTacletGoalTemplate(TacletGoalTemplate goal) {
	if (goal instanceof AntecSuccTacletGoalTemplate) {
	    throw new IllegalArgumentException("Tried to add a AntecSucc"+
					       "GoalTemplate to a Rewrite"+
					       "Taclet");	    
	}
	
	goals = goals.prepend(goal);
    }


    public void addGoalTerm(Term goalTerm) {
        final TacletGoalTemplate axiomTemplate =
                new RewriteTacletGoalTemplate(goalTerm);
        addTacletGoalTemplate(axiomTemplate);
    }


    /** builds and returns the Taclet that is specified by
     * former set... / add... methods. If no name is specified then
     * an Taclet with an empty string name is build. No specifications
     * for variable conditions, goals or heuristics imply that the
     * corresponding parts of the Taclet are empty. No specification for
     * the if-sequence is represented as a sequent with two empty
     * semisequences. No specification for the interactive or
     * recursive flags imply that the flags are not set. 
     * No specified find part causes an IllegalStateException.
     */
    @Override
    public Taclet getTaclet(){
	return getRewriteTaclet();
    }
}
