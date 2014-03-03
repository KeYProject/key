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


package de.uka.ilkd.key.rule;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.BoundVarsVisitor;
import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.tacletbuilder.FindTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGoalTemplate;


/** 
 * An abstract class to represent Taclets with a find part. This means, they
 * have to be attached to a formula or term of the sequent. This class is
 * extended by several subclasses to distinct between taclets that have to
 * attached to a top level formula of the antecedent ({@link AntecTaclet}),
 * to the succedent ({@link SuccTaclet}) or to an arbitrary term that matches
 * the find part somewhere in the sequent ({@link RewriteTaclet}).  
 */ 
public abstract class FindTaclet extends Taclet {

    /** contains the find term */
    protected Term find;

    /** Set of schemavariables of the if and the (optional) find part */
    private ImmutableSet<SchemaVariable> ifFindVariables = null;

    /** this method is used to determine if top level updates are
     * allowed to be ignored. This is the case if we have an Antec or
     * SuccTaclet but not for a RewriteTaclet
     * @return true if top level updates shall be ignored 
     */
    protected abstract boolean ignoreTopLevelUpdates();

    
    /** creates a FindTaclet 
     * @param name the Name of the taclet
     * @param applPart the TacletApplPart that contains the if-sequent, the
     * not-free and new-vars conditions 
     * @param goalTemplates a IList<TacletGoalTemplate> that contains all goaltemplates of
     * the taclet (these are the instructions used to create new goals when
     * applying the Taclet)
     * @param ruleSets a IList<RuleSet> that contains all rule sets the Taclet
     *      is attached to
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive,
     * recursive or something like that
     * @param find the Term that is the pattern that has to be found in a
     * sequent and the places where it matches the Taclet can be applied
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the
     * prefix for each SchemaVariable in the Taclet
     */
    public FindTaclet(Name name, TacletApplPart applPart,  
		      ImmutableList<TacletGoalTemplate> goalTemplates, 
		      ImmutableList<RuleSet> ruleSets,
		      TacletAttributes attrs, Term find,
		      ImmutableMap<SchemaVariable,TacletPrefix> prefixMap,
		      ImmutableSet<Choice> choices){
	super(name, applPart, goalTemplates, ruleSets, attrs, prefixMap,
	      choices);
	this.find = find;
    }
    
    /** returns the find term of the taclet to be matched */
    public Term find() {
	return find;
    }
    
    /**
     * ignores a possible update prefix
     * @param term the term to be matched
     * @param template the pattern term
     * @param matchCond the accumulated match conditions for a successful match
     * @param services the Services
     * @return a pair of updated match conditions and the unwrapped term without the ignored updates (Which have been added to the update context in the match conditions)
     */
    private IgnoreUpdateMatchResult matchAndIgnoreUpdatePrefix(final Term term,
            final Term template, MatchConditions matchCond, final TermServices services) {

        final Operator sourceOp   = term.op ();
        final Operator templateOp = template.op ();

        if ( sourceOp instanceof UpdateApplication
                && !(templateOp instanceof UpdateApplication) ) {
            // updates can be ignored
            Term update = UpdateApplication.getUpdate(term);
            matchCond = matchCond
                    .setInstantiations ( matchCond.getInstantiations ().
                            addUpdate (update, term.getLabels()) );
            return matchAndIgnoreUpdatePrefix(UpdateApplication.getTarget(term), 
                    template, matchCond, services);       
        } else {
            return new IgnoreUpdateMatchResult(term, matchCond);
        }
    }


    /** 
     * matches the given term against the taclet's find term and
     * @param term the Term to be matched against the find expression 
     * of the taclet
     * @param matchCond the MatchConditions with side conditions to be 
     * satisfied, eg. partial instantiations of schema variables; before
     * calling this method the constraint contained in the match conditions
     * must be ensured to be satisfiable, i.e.
     *       <tt> matchCond.getConstraint ().isSatisfiable () </tt>
     * must return true
     * @param services the Services 
     * @return the found schema variable mapping or <tt>null</tt> if 
     * the matching failed
     */
    public MatchConditions matchFind(Term term,
            MatchConditions matchCond,
            Services services) {
        
        if (ignoreTopLevelUpdates()) {
            IgnoreUpdateMatchResult resultUpdateMatch = 
                    matchAndIgnoreUpdatePrefix(term, find(), matchCond, services);
            term = resultUpdateMatch.termWithoutMatchedUpdates;
            matchCond = resultUpdateMatch.matchCond;
        }
        
        return match(term, find(), matchCond, services);
    }

    /** CONSTRAINT NOT USED 
     * applies the replacewith part of Taclets
     * @param gt TacletGoalTemplate used to get the replaceexpression 
     * in the Taclet
     * @param goal the Goal where the rule is applied
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected abstract void applyReplacewith(TacletGoalTemplate gt, Goal goal,
					     PosInOccurrence posOfFind,
					     Services services,
					     MatchConditions matchCond);


    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param add the Sequent to be added
     * @param goal the Goal to be updated
     * @param posOfFind the PosInOccurrence describes the place where to add
     * the semisequent 
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected abstract void applyAdd(Sequent add, Goal goal,
				     PosInOccurrence posOfFind,
				     Services services,
				     MatchConditions matchCond);


    /**  
     * the rule is applied on the given goal using the
     * information of rule application. 
     * @param goal the goal that the rule application should refer to.
     * @param services the Services encapsulating all java information
     * @param ruleApp the taclet application that is executed.
     */
    public ImmutableList<Goal> apply(Goal     goal,
			    Services services,
			    RuleApp  ruleApp) {

	// Number without the if-goal eventually needed
	int                          numberOfNewGoals = goalTemplates().size();

	TacletApp                    tacletApp        = (TacletApp) ruleApp;
	MatchConditions              mc               = tacletApp.matchConditions ();

	ImmutableList<Goal>                   newGoals         =
	    checkIfGoals ( goal,
			   tacletApp.ifFormulaInstantiations (),
			   mc,
			   numberOfNewGoals );
	
	Iterator<TacletGoalTemplate> it               = goalTemplates().iterator();
	Iterator<Goal>               goalIt           = newGoals.iterator();

	while (it.hasNext()) {
	    TacletGoalTemplate gt          = it    .next();
	    Goal               currentGoal = goalIt.next();
	    // add first because we want to use pos information that
	    // is lost applying replacewith
	    applyAdd(         gt.sequent(),
			      currentGoal,
			      tacletApp.posInOccurrence(),
			      services,
			      mc );

	    applyReplacewith( gt,
			      currentGoal,
			      tacletApp.posInOccurrence(),
			      services,
			      mc );

	    applyAddrule(     gt.rules(),
			      currentGoal,
			      services,
			      mc );

	    
	    applyAddProgVars( gt.addedProgVars(),
			      currentGoal,
                              tacletApp.posInOccurrence(),
                              services,
			      mc);
                               
            currentGoal.setBranchLabel(gt.name());
	}

	return newGoals;
    }

    StringBuffer toStringFind(StringBuffer sb) {
	return sb.append("\\find(").
	    append(find().toString()).append(")\n");
    }


    /**
     * returns a representation of the Taclet with find part as String
     * @return string representation
     */
    public String toString() {
	if (tacletAsString == null) {
	    StringBuffer sb = new StringBuffer();
	    sb = sb.append(name()).append(" {\n");
	    sb = toStringIf(sb);
	    sb = toStringFind(sb);
	    sb = toStringVarCond(sb);
	    sb = toStringGoalTemplates(sb);
	    sb = toStringRuleSets(sb);
	    sb = toStringAttribs(sb); 
	    tacletAsString = sb.append("}").toString();
	}
	return tacletAsString;
    }


    /**
     * @return Set of schemavariables of the if and the (optional)
     * find part
     */
    public ImmutableSet<SchemaVariable> getIfFindVariables () {
	if ( ifFindVariables == null ) {
	    TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector ();
	    find ().execPostOrder ( svc );
	    
	    ifFindVariables             = getIfVariables ();
	    Iterator<SchemaVariable> it = svc.varIterator ();
	    while ( it.hasNext () )
		ifFindVariables = ifFindVariables.add ( it.next () );
	}

	return ifFindVariables;
    }


    protected Taclet setName(String s, FindTacletBuilder b) {
	return super.setName(s, b); 
    }


    /**
     * returns the variables that occur bound in the find part
     */
    protected ImmutableSet<QuantifiableVariable> getBoundVariablesHelper() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(find());
        return bvv.getBoundVariables();
    }
    
    private static final class IgnoreUpdateMatchResult {
        public Term termWithoutMatchedUpdates;
        public MatchConditions matchCond;

        public IgnoreUpdateMatchResult(Term term, MatchConditions matchCond) {
            this.termWithoutMatchedUpdates = term;
            this.matchCond = matchCond;
        }
    }
    
} 
