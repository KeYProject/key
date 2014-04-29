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

package de.uka.ilkd.key.rule.tacletbuilder;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.SuccTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApplPart;


/** class builds SuccTaclet objects.*/
public class SuccTacletBuilder extends FindTacletBuilder {

    private boolean ignoreTopLevelUpdates = true;

    /** sets the <I>find</I> of the Taclet that is to build to the given
     * term, if the sort of the given term is of Sort.FORMULA otherwise
     * nothing happens.
     * @return this SuccTacletBuilder
     */ 
    public SuccTacletBuilder setFind(Term findTerm) {
	if (findTerm.sort()==Sort.FORMULA) 
	    find=findTerm;
	checkContainsFreeVarSV(findTerm, this.getName(), "find term");	
	return this;
    }


    /** adds a new goal descriptions to the goal descriptions of the Taclet.
     * the TacletGoalTemplate must not be an RewriteTacletGoalTemplate,
     * otherwise an illegal argument exception is thrown.
     */
    public void addTacletGoalTemplate(TacletGoalTemplate goal) {
	if (goal instanceof RewriteTacletGoalTemplate) {
	    throw new TacletBuilderException(this, 
                    "Tried to add a RewriteTaclet"+
                    "GoalTemplate to a Succ"+
	    "Taclet");	    
	}
	goals=goals.prepend(goal);
    }


    /** builds and returns the SuccTaclet that is specified by
     * former set... / add... methods. If no name is specified then
     * an Taclet with an empty string name is build. No specifications
     * for variable conditions, goals or heuristics imply that the
     * corresponding parts of the Taclet are empty. No specification for
     * the if-sequence is represented as a sequent with two empty
     * semisequents. No specification for the interactive or
     * recursive flags imply that the flags are not set. 
     * No specified find part causes an IllegalStateException.
     * Throws an
     * TacletBuilderException if a bound SchemaVariable occurs more than once in if
     * and find or an InvalidPrefixException if the building of the Taclet 
     * Prefix fails.
     */
    public SuccTaclet getSuccTaclet(){
	if (find == null) {
	    throw new TacletBuilderException(this, "No find part specified");
	    
	}
	checkBoundInIfAndFind();
	final TacletPrefixBuilder prefixBuilder = 
            new TacletPrefixBuilder(this);
	prefixBuilder.build();
	return new SuccTaclet(name, 
			      new TacletApplPart(ifseq,
						 varsNew,
						 varsNotFreeIn,
						 varsNewDependingOn,
						 variableConditions),
			      goals, ruleSets,
			      attrs,
			      find,
                              ignoreTopLevelUpdates,
			      prefixBuilder.getPrefixMap(),
			      choices);
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
    public Taclet getTaclet(){
	return getSuccTaclet();
    }


    public void setIgnoreTopLevelUpdates(boolean ignore) {
        ignoreTopLevelUpdates = ignore;
    }
}