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

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.BoundUniquenessChecker;
import de.uka.ilkd.key.rule.NoFindTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApplPart;


/** 
 * Due to the immutability of {@link Taclet}s, they are created in the parsers 
 * using {@link TacletBuilder}s. This builder is used for 
 * {@link NoFindTaclet} rules. Besides this some tests are performed that avoid 
 * some common errors on applicability of taclets.  
 */
public class NoFindTacletBuilder extends TacletBuilder {


    /** builds and returns the RewriteTaclet that is specified by
     * former set... / add... methods. If no name is specified then
     * an Taclet with an empty string name is build. No specifications
     * for variable conditions, goals or heuristics imply that the
     * corresponding parts of the Taclet are empty. No specification for
     * the if-sequent is represented as a sequent with two empty
     * semisequences. No specification for the interactive or
     * recursive flags imply that the flags are not set. 
     */
    public NoFindTaclet getNoFindTaclet(){

	TacletPrefixBuilder prefixBuilder=new TacletPrefixBuilder(this);
	prefixBuilder.build();
	return new NoFindTaclet(this.name, 
				new TacletApplPart(ifseq,
						   varsNew,
						   varsNotFreeIn,
						   varsNewDependingOn,
						   variableConditions),
				goals, ruleSets,
				attrs,
				prefixBuilder.getPrefixMap(),
				choices);
    }


    /** 
     * adds a new goal descriptions to the goal descriptions of the Taclet.
     * @param goal the TacletGoalTemplate specifying all the changes to be made
     * to achieve one of the resulting goals
     */
    public void addTacletGoalTemplate(TacletGoalTemplate goal) {
	goals = goals.prepend(goal);
    }


    public void addGoalTerm(Term goalTerm) {
        final SequentFormula axiomSf = new SequentFormula(goalTerm);
        final Semisequent axiomSemiSeq =
                Semisequent.EMPTY_SEMISEQUENT.insertFirst(axiomSf).semisequent();
        final Sequent axiomSeq = Sequent.createAnteSequent(axiomSemiSeq);
        final TacletGoalTemplate axiomTemplate =
                new AntecSuccTacletGoalTemplate(
                axiomSeq, ImmutableSLList.<Taclet>nil(), Sequent.EMPTY_SEQUENT);
        addTacletGoalTemplate(axiomTemplate);
    }


    /**
     * checks that a variableSV occurrs at most once in a quantifier of the
     * ifs and finds and throws an exception otherwise
     */
    protected void checkBoundInIfAndFind() {
	final BoundUniquenessChecker ch = 
            new BoundUniquenessChecker(ifSequent());
	if (!ch.correct()) {
	    throw new TacletBuilderException
            (this, "A bound SchemaVariable occurs twice in if.");
	}
    }

    
    /**
     * builds and returns the Taclet that is specified by
     * former set... / add... methods. If no name is specified then
     * an Taclet with an empty string name is build. No specifications
     * for variable conditions, goals or heuristics imply that the
     * corresponding parts of the Taclet are empty. No specification for
     * the if-sequent is represented as a sequent with two empty
     * semisequences. No specification for the interactive or
     * recursive flags imply that the flags are not set. May throw an
     * TacletBuilderException if a bound SchemaVariable occurs more than once in if
     * and find.
     */
    public Taclet getTaclet(){
	checkBoundInIfAndFind();
	return getNoFindTaclet();
    }
}
