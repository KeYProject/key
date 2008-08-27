// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
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
    private SetOfSchemaVariable ifFindVariables = null;

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
     * @param goalTemplates a ListOfTacletGoalTemplate that contains all goaltemplates of
     * the taclet (these are the instructions used to create new goals when
     * applying the Taclet)
     * @param ruleSets a ListOfRuleSet that contains all rule sets the Taclet
     *      is attached to
     * @param constraint the Constraint of the Taclet (has to be fulfilled in
     * order to achieve this Taclet)
     * @param attrs the TacletAttributes encoding if the Taclet is non-interactive,
     * recursive or something like that
     * @param find the Term that is the pattern that has to be found in a
     * sequent and the places where it matches the Taclet can be applied
     * @param prefixMap a MapFromSchemaVariableToTacletPrefix that contains the
     * prefix for each SchemaVariable in the Taclet
     */
    public FindTaclet(Name name, TacletApplPart applPart,  
		      ListOfTacletGoalTemplate goalTemplates, 
		      ListOfRuleSet ruleSets,
		      Constraint constraint, TacletAttributes attrs,
		      Term find,
		      MapFromSchemaVariableToTacletPrefix prefixMap,
		      SetOfChoice choices){
	super(name, applPart, goalTemplates, ruleSets, constraint, attrs,
	      prefixMap, choices);
	this.find = find;
    }
    
    /** returns the find term of the taclet to be matched */
    public Term find() {
	return find;
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
     * @param userConstraint a Constraint derived from user defined 
     * instantiations of meta variables
     * @return the found schema variable mapping or <tt>null</tt> if 
     * the matching failed
     */
    public MatchConditions matchFind(Term term,
            MatchConditions matchCond,
            Services services,
            Constraint userConstraint) {
        return match(term, find(), 
                ignoreTopLevelUpdates(),
                matchCond, services, userConstraint);
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

        // reklov
        // START TEMPORARY DOWNWARD COMPATIBILITY
        ((InnerVariableNamer) services.getVariableNamer()).
                setOldProgVarProposals((Name) tacletApp.instantiations().
                getInstantiation(new NameSV("_NAME_PROG_VARS")));
        // END TEMPORARY DOWNWARD COMPATIBILITY

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
    public SetOfSchemaVariable getIfFindVariables () {
	if ( ifFindVariables == null ) {
	    TacletSchemaVariableCollector svc = new TacletSchemaVariableCollector ();
	    find ().execPostOrder ( svc );
	    
	    ifFindVariables             = getIfVariables ();
	    IteratorOfSchemaVariable it = svc.varIterator ();
	    while ( it.hasNext () )
		ifFindVariables = ifFindVariables.add ( it.next () );
	}

	return ifFindVariables;
    }


    protected Taclet setName(String s, FindTacletBuilder b) {
	return super.setName(s, b); 
    }

    /**
     * Determine whether a replacewith-part is really supposed to modify
     * concerned formulas when applying a taclet (otherwise copies of the
     * formulas are created). Copies are created whenever the constraint of the
     * new formulas is stronger than the conjunction of the original
     * find-formula constraint and the user constraint. (Taking the user
     * constraint into account at this point ensures that the existence of the
     * user constraint is transparent to the user, and is a temporary solution
     * to cope with the absence of disunification constraints).
     * 
     * UPDATE: for the time being we are only considering the old constraint of
     * the formula (as the user constraint is more or less disable in
     * <code>TacletApp. canUseMVAPosteriori</code> right now)
     * 
     * @param goal
     *            the goal to which the taclet is applied
     * @param posOfFind
     *            position of the find-formula (which is the formula whose
     *            constraint is considered as the original formula constraint)
     * @param matchCond
     *            results of matching the taclet, in particular the new
     *            constraint that is attached to formulas added by replacewith
     * @return true iff replacewith is supposed to create copies of concerned
     *         formulas
     */
    protected boolean createCopies (Goal goal,
                                    PosInOccurrence posOfFind,
                                    MatchConditions matchCond) {
//        final Proof proof = goal.proof (); 
//        final Constraint userConstraint =
//            proof.getUserConstraint ().getConstraint ();
        final Constraint oriConstraint =
            posOfFind.constrainedFormula ().constraint ();
//        final Constraint combinedConstraint =
//            userConstraint.join ( oriConstraint, proof.getServices() );
        final Constraint newConstraint = matchCond.getConstraint ();
        return !newConstraint.isAsWeakAs ( oriConstraint );
    }
    
    
    /** returns the variables in a Taclet with a read access
    */
    public ListOfSchemaVariable readSet() {

	//List variables have to be collected to
	ListOfSchemaVariable readFromVarialbes = 
            SLListOfSchemaVariable.EMPTY_LIST;

	//List of Variables in find-part
	TacletSchemaVariableCollector tvarColl1 = new TacletSchemaVariableCollector() {
            public void visit(Term t) {	
	        if (t.op() instanceof Modality || 
                    t.op() instanceof ModalOperatorSV) {
	            varList = collectSVInProgram(t.javaBlock(),
					         varList);
	        }
	        for (int j=0; j<t.arity(); j++) {
	            for (int i=0;i<t.varsBoundHere(j).size();i++) {
		        if (t.varsBoundHere(j).getQuantifiableVariable(i) 
		            instanceof SchemaVariable) {
		            varList = varList.prepend
			        ((SchemaVariable)t.varsBoundHere(j)
			         .getQuantifiableVariable(i)); 
		        }
	            }
	        }
            }
        };
	tvarColl1.visit(find()); 

	//List of variables im add & replaceWith-Part
	TacletSchemaVariableCollector tvarColl2 = new TacletSchemaVariableCollector() {
    	    public void visit(Term t) {	
		if (t.op() instanceof SchemaVariable) 
                    varList=varList.prepend((SchemaVariable)t.op());
    	    }	
        };
	tvarColl2.visitGoalTemplates(this, false); 
	
        // build intersection
	IteratorOfSchemaVariable it1 = tvarColl1.varIterator();
	while(it1.hasNext()){
	        SchemaVariable sv1 = it1.next();
		IteratorOfSchemaVariable it2 = tvarColl2.varIterator();

		while(it2.hasNext()){
		    SchemaVariable sv2 = it2.next();

		    if(sv1 == sv2){
			if(writeSet().head()!= null) {
			    //if the variable belongs to the WriteSet, 
                            //remove it from the ReadSet
			    if (writeSet().head() != sv1 )
			       readFromVarialbes = readFromVarialbes.prepend(sv1);
			}
			else readFromVarialbes = readFromVarialbes.prepend(sv1);
			break; //variable found, no need to keep searching
	            }
		}
	}
	return readFromVarialbes; 
    }

    /** 
     * returns the variable in a Taclet to which is written to
     */
    public ListOfSchemaVariable writeSet() {
	IteratorOfTacletGoalTemplate it = goalTemplates().iterator();
	ListOfSchemaVariable updateVar = SLListOfSchemaVariable.EMPTY_LIST; 
	Term replWith = null; 
	
	while (it.hasNext()){
	    TacletGoalTemplate goalTemp = it.next();

	    if(goalTemp instanceof RewriteTacletGoalTemplate){
		replWith = ((RewriteTacletGoalTemplate)goalTemp).replaceWith();

		if (replWith.op() instanceof IUpdateOperator){
		    try{                
		        updateVar = updateVar.prepend((SchemaVariable)replWith.sub(0).op());
		    } catch(ClassCastException e) {
		        System.err.println(name()+" "+replWith.sub(0).op().getClass());
		    }
		}
	    }
	}
	return updateVar;
    } 

    /**
     * returns the variables that occur bound in the find part
     * @return the variables that occur bound in the find part
     */
    protected SetOfQuantifiableVariable getBoundVariablesHelper() {
        final BoundVarsVisitor bvv = new BoundVarsVisitor();
        bvv.visit(find());
        return bvv.getBoundVariables();
    }
    
} 
