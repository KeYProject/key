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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMap;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** 
 * A RewriteTaclet represents a taclet, whose find can be matched against any
 * term in the sequent no matter where it occurs. The only constraint to be
 * fulfilled is that the term matches the structure described by the term of the
 * find-part.
 */
public final class RewriteTaclet extends FindTaclet {

    /** does not pose state restrictions on valid matchings */
    public static final int NONE = 0;

    /** all taclet consituents must appear in the same state 
     * (and not below a modality (for efficiency reasons)) */
    public static final int SAME_UPDATE_LEVEL = 1;

    /** all taclet consituents must be in the same state 
     * as the sequent */
    public static final int IN_SEQUENT_STATE = 2;
    

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
    private int stateRestriction;


    /**
     * creates a Schematic Theory Specific Rule (Taclet) with the given
     * parameters that represents a rewrite rule.  
     * @param name the Name of the Taclet 
     * @param applPart the TacletApplPart that contains the application part of an Taclet that is
     * the if-sequent, the variable conditions
     * @param goalTemplates a list of goal descriptions.
     * @param ruleSets a list of rule sets for the Taclet
     * @param constraint the Constraint under which the Taclet is valid
     * @param attrs the TacletAttributes; these are boolean values
     * indicating a noninteractive or recursive use of the Taclet. 
     * @param find the find term of the Taclet
     * @param prefixMap a ImmMap<SchemaVariable,TacletPrefix> that contains the
     * prefix for each SchemaVariable in the Taclet
     * @param p_stateRestriction an int defining state restrictions of the taclet
     * (required for location check)
     * @param choices the SetOf<Choices> to which this taclet belongs to
     */
    public RewriteTaclet(Name name, TacletApplPart applPart,  
			 ImmutableList<TacletGoalTemplate>  goalTemplates, 
			 ImmutableList<RuleSet>             ruleSets,
			 Constraint                constraint,
			 TacletAttributes          attrs,
			 Term                      find, 
			 ImmutableMap<SchemaVariable,TacletPrefix> prefixMap,
			 int                       p_stateRestriction,
			 ImmutableSet<Choice> choices){
	super(name, applPart, goalTemplates, ruleSets, constraint,
	      attrs, find, prefixMap, choices);
	stateRestriction = p_stateRestriction;
	
	cacheMatchInfo();
    }	

      
    /** 
     * this method is used to determine if top level updates are
     * allowed to be ignored. This is the case if we have an Antec or
     * SuccTaclet but not for a RewriteTaclet
     * @return true if top level updates shall be ignored 
     */
    protected boolean ignoreTopLevelUpdates() {
	return false;
    }
    
    /**
     * returns the int encoding the kind of state restriction this rewrite 
     * taclet must obey     
     * @return the int encoding the kind of state restriction this rewrite 
     * taclet must obey      
     */
    public int getStateRestriction () {
	return stateRestriction;
    }


    /**
     * the top level operator has to be a simultaneous update. This method 
     * checks if the assignment pairs of the update contain free logic
     * variables and gives a veto if positive
     * @param t the Term to check
     * @return false if vetoing 
     */
    private boolean veto (Term t) {
        return t.freeVars ().size () > 0;
    }

    /**
     * For taclets with <code>getSameUpdatePrefix ()</code>, collect
     * the updates above <code>p_pos</code> and add them to the update
     * context of the instantiations object <code>p_mc</code>.
     * @return the new instantiations with the additional updates, or
     * <code>null</code>, if program modalities appear above
     * <code>p_pos</code>
     */
    public MatchConditions checkUpdatePrefix
	( PosInOccurrence p_pos,
	  MatchConditions p_mc,
	  Services        p_services,
	  Constraint      p_userConstraint ) {
	if ( getStateRestriction() == NONE)  
	    return p_mc;

	SVInstantiations svi = p_mc.getInstantiations ();
	if ( p_pos.posInTerm () != null ) {
	    PIOPathIterator it = p_pos.iterator ();
	    Operator        op;

	    while ( it.next () != -1 ) {
		final Term t = it.getSubTerm ();
		op = t.op ();

		if ( op instanceof UpdateApplication &&
		     it.getChild () == ((UpdateApplication)op).targetPos()) {		    
		    if ( getStateRestriction() == IN_SEQUENT_STATE || veto(t) ) {
			return null;
		    } else {
			Term update = ((UpdateApplication) op).getUpdate(t);
			svi = svi.addUpdate ( update );
		    }
		    
		}
		else if ( op instanceof Modality ||
			  op instanceof ModalOperatorSV)
		    return null;
	    }
	}

	return p_mc.setInstantiations ( svi );
    }

    /**
     * does the work for applyReplacewith (wraps recursion) 
     */
    private Term replace(Term term, Term with, IntIterator it,
			 Services services, MatchConditions mc, 
                         Sort maxSort) {
	if (it.hasNext()) {	    
	    int sub = it.next();
	    
	    final Term[] subs = new Term[term.arity()];
	    
	    for (int i=0, arity = term.arity(); i<arity; i++) {
		
                if (i!=sub) {
		    subs[i] = term.sub(i);
		} else {                    
                    final Sort newMaxSort = TermHelper.getMaxSort(term, i, services);
		    subs[i] = replace(term.sub(i), with, it, services, 
		            mc, newMaxSort);
		}
	    }	    	    	    	    	    
 	    
	    return TermFactory.DEFAULT.createTerm(term.op(), 
	            subs, term.boundVars(), term.javaBlock());
	} 
                                      
	with = syntacticalReplace(with, services, mc);   

               
	if (!with.sort().extendsTrans(maxSort)) {
	    with = TermBuilder.DF.cast(services, maxSort, with);
	}
        
	return with;
    }


    /**
     * Check if p_pos contains an explicit metavariable instantiation,
     * and creates in this case a new simple term by replacing the
     * metavariable with the instantiation
     */
    private PosInOccurrence flatten ( PosInOccurrence p_pos,
				      Services        p_services) {
	if ( p_pos.termBelowMetavariable () != null ) {
	    assert false : "metavariables are disabled";
	    Term flatTerm = replace ( p_pos.constrainedFormula ().formula (),
				      p_pos.termBelowMetavariable (),
				      p_pos.posInTerm ().iterator (),
				      p_services,
				      MatchConditions.EMPTY_MATCHCONDITIONS, 
                                      Sort.FORMULA);

	    PosInOccurrence pos = new PosInOccurrence
		( new ConstrainedFormula ( flatTerm,
					   p_pos.constrainedFormula ().constraint () ),
		  p_pos.posInTerm (),
		  p_pos.isInAntec() );

	    IntIterator it = p_pos.posInTermBelowMetavariable ().iterator ();
	    while ( it.hasNext () )
		pos = pos.down ( it.next () );

	    return pos;
	}

	return p_pos;
    }
    

    private ConstrainedFormula applyReplacewithHelper(
	    				RewriteTacletGoalTemplate gt, 
				 	PosInOccurrence    posOfFind,
				 	Services           services,
				 	MatchConditions    matchCond) {
	PosInOccurrence flatPos = flatten ( posOfFind, services );

	Term term = flatPos.constrainedFormula().formula();
	IntIterator it = flatPos.posInTerm().iterator();
	Term rwTemplate=((RewriteTacletGoalTemplate)gt).replaceWith();

	Term formula = replace(term, 
		       	       rwTemplate, 
		       	       it, 
		       	       services, 
		       	       matchCond, 
		       	       term.sort());
	return new ConstrainedFormula(formula);
    }
    
    
    //XXX
    public ConstrainedFormula getRewriteResult(Services services, 
	    				       TacletApp app) {
	assert goalTemplates().size() == 1;
	assert ifSequent().isEmpty();
	assert getStateRestriction() == NONE;
	assert app.complete();
	RewriteTacletGoalTemplate gt 
		= (RewriteTacletGoalTemplate) goalTemplates().head();
	return applyReplacewithHelper(gt, 
				      app.posInOccurrence(), 
				      services, 
				      app.matchConditions());
    }


    /** CONSTRAINT NOT USED 
     * applies the replacewith part of Taclets
     * @param gt TacletGoalTemplate used to get the replaceexpression in the Taclet
     * @param goal the Goal where the rule is applied
     * @param posOfFind the PosInOccurrence belonging to the find expression
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected void applyReplacewith(TacletGoalTemplate gt, 
				    Goal               goal,
				    PosInOccurrence    posOfFind,
				    Services           services,
				    MatchConditions    matchCond) {
	if ( gt instanceof RewriteTacletGoalTemplate ) {
            ConstrainedFormula cf 
            	= applyReplacewithHelper((RewriteTacletGoalTemplate)gt, 
        	    			         posOfFind, 
        	    			         services, 
        	    			         matchCond);
	    assert matchCond.getConstraint () == Constraint.BOTTOM : "metavariables are disabled";
	    if ( createCopies ( goal, posOfFind, matchCond ) ) {
                goal.addFormula ( cf, posOfFind );
	    } else {
                goal.changeFormula ( cf, posOfFind );
	    }
	} else {
	    // Then there was no replacewith...
	    // This is strange in a RewriteTaclet, but who knows...
	}
    }

    /**
     * adds the sequent of the add part of the Taclet to the goal sequent
     * @param add the Sequent to be added
     * @param goal the Goal to be updated
     * @param posOfFind the PosInOccurrence describes the place where to add
     * the semisequent
     * @param services the Services encapsulating all java information
     * @param matchCond the MatchConditions with all required instantiations 
     */
    protected void applyAdd(Sequent         add, 
			    Goal            goal,
			    PosInOccurrence posOfFind,
			    Services        services,
			    MatchConditions matchCond) {
	if (posOfFind.isInAntec()) {
	    addToAntec(add.antecedent(), goal, posOfFind, services, matchCond);
	    addToSucc(add.succedent(), goal, null, services, matchCond);
	} else {
	    addToAntec(add.antecedent(), goal, null, services, matchCond);	
	    addToSucc(add.succedent(), goal, posOfFind, services, matchCond);
	}
    }
    
    protected Taclet setName(String s) {
	final RewriteTacletBuilder b = new RewriteTacletBuilder();
	b.setFind(find());
	b.setStateRestriction ( getStateRestriction() );
	return super.setName(s, b);
    }


    StringBuffer toStringFind(StringBuffer sb) {
	StringBuffer res = super.toStringFind ( sb );
	if ( getStateRestriction() == SAME_UPDATE_LEVEL )
	    res.append ( "\\sameUpdateLevel\n" );
	else if ( getStateRestriction() == IN_SEQUENT_STATE )
	    res.append ( "\\inSequentState\n" );
	return res;
    }
}
