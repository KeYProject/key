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

import java.util.Arrays;
import java.util.HashSet;

import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.conditions.NewDepOnAnonUpdates;
import de.uka.ilkd.key.rule.inst.*;
import de.uka.ilkd.key.util.Debug;

/** 
 * A TacletApp object contains information required for a concrete application. 
 * These information may consist of
 * <ul>
 * <li> instantiations of the schemavariables </li>
 * <li> position of the find term </li>
 * </ul>
 * Its methods <code>complete</code> or <code>sufficientlyComplete</code> are
 * used to determine if the information is complete or at least sufficient
 * (can be completed using meta variables) complete, so that is can be
 * applied. 
 */
public abstract class TacletApp implements RuleApp {

    /** the taclet for which the application information is collected */
    private Taclet taclet;

    /** 
     * contains the instantiations of the schemavarioables of the
     * Taclet 
     */
    protected SVInstantiations instantiations;

    /**
     * constraint under which the taclet application can be performed
     */
    protected Constraint       matchConstraint;
	
    /**
     * metavariables that have been created during the matching
     */
    protected SetOfMetavariable matchNewMetavariables;

    /**
     * choosen instantiations for the if sequent formulas
     */
    ListOfIfFormulaInstantiation ifInstantiations = null;

    /** set of schemavariables that appear in the Taclet and need to be
     * instantiated but are not instantiated yet. This means
     * SchemaVariables in addrule-sections have to be ignored
     */
    private SetOfSchemaVariable missingVars = null;

    /** subset of missingVars that cannot be instantiated using
     * metavariables
     */
    private SetOfSchemaVariable neededMissingVars = null;

    /**
     * the instantiations of the following SVs must not be changed;
     * they must not be instantiated with metavariables either
     */
    protected SetOfSchemaVariable fixedVars = SetAsListOfSchemaVariable.EMPTY_SET;
    /**
     * the update context given by the current instantiations must not
     * be changed
     */
    protected boolean updateContextFixed = false;
    
    /** constructs a TacletApp for the given taclet, with an empty instantiation 
     *	map 
     */
    TacletApp(Taclet taclet) {
	this ( taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS, Constraint.BOTTOM,
	       SetAsListOfMetavariable.EMPTY_SET, null );
    }

    TacletApp ( Taclet                       taclet,
		SVInstantiations             instantiations,
		Constraint                   matchConstraint,
		SetOfMetavariable            matchNewMetavariables,
		ListOfIfFormulaInstantiation ifInstantiations ) {
	this.taclet                = taclet;
	this.instantiations        = instantiations;
	this.matchConstraint       = matchConstraint;
	this.matchNewMetavariables = matchNewMetavariables;
	this.ifInstantiations      = ifInstantiations;
    }

    /** constructs a TacletApp for the given taclet. With some information about
     * required instantiations.
     */
    TacletApp(Taclet taclet, SVInstantiations instantiations) {
	this ( taclet, instantiations, Constraint.BOTTOM,
	       SetAsListOfMetavariable.EMPTY_SET, null );
    }

    /** collects all bound variables above the occurrence of the schemavariable
     * whose prefix is given
     * @param prefix the TacletPrefix of the schemavariable
     * @param instantiations the SVInstantiations so that the
     * find(if)-expression matches 
     * @return set of the bound variables 
     */
    protected static SetOfQuantifiableVariable 
	boundAtOccurrenceSet(TacletPrefix prefix,
			     SVInstantiations instantiations) {	
	return collectPrefixInstantiations(prefix, 
					   instantiations);
    }


    /** collects all bound variables above the occurrence of the schemavariable
     * whose prefix is given
     * @param prefix the TacletPrefix of the schemavariable
     * @param instantiations the SVInstantiations so that the
     * find(if)-expression matches 
     * @param pos the posInOccurrence describing the position of the
     * schemavariable 
     * @return set of the bound variables 
     */
    protected static SetOfQuantifiableVariable
	boundAtOccurrenceSet ( TacletPrefix     prefix,
			       SVInstantiations instantiations,
			       PosInOccurrence  pos ) {
    
	SetOfQuantifiableVariable result =
	    boundAtOccurrenceSet(prefix, instantiations);
    
	if ( prefix.context () )
	    result = result.union ( collectBoundVarsAbove ( pos ) );
    
	return result;		
    }


    /** collects all those logic variable that are instances of the variableSV
     * of the given prefix
     * @param pre the TacletPrefix of a SchemaVariable that is bound
     * @param instantiations the SVInstantiations to look at
     * @return the set of the logic variables whose elements are the
     * instantiations of a bound SchemaVariable appearing in the TacletPrefix
     */ 
    private static SetOfQuantifiableVariable collectPrefixInstantiations
	(TacletPrefix pre, SVInstantiations instantiations) {

	SetOfQuantifiableVariable instanceSet 
	    = SetAsListOfQuantifiableVariable.EMPTY_SET;
	IteratorOfSchemaVariable it = pre.prefix().iterator();
	while (it.hasNext()) {
	    SchemaVariable var = it.next();
	    instanceSet = 
		instanceSet.add((LogicVariable)
				((Term)instantiations.getInstantiation(var)).op());
	}
	return instanceSet;
    }


    /** returns the taclet the application information is collected for
     * @return the Taclet the application information is collected for
     */
    public Taclet taclet() {
	return taclet;
    }

    /** returns the rule the application information is collected for
     * @return the Rule the application information is collected for
     */
    public Rule rule() {
	return taclet;
    }

    /**
     * returns the instantiations for the application of the Taclet at the
     * specified position.
     * @return the SVInstantiations needed to instantiate the Taclet
     */
    public SVInstantiations instantiations() {
	return instantiations;
    }


    public Constraint       constraint () {
	return matchConstraint;
    }


    public SetOfMetavariable newMetavariables () {
	return matchNewMetavariables;
    }


    public MatchConditions  matchConditions () {
	return new MatchConditions ( instantiations   (),
				     constraint       (),
				     newMetavariables (),
                                     RenameTable.EMPTY_TABLE);
    }


    public ListOfIfFormulaInstantiation ifFormulaInstantiations () {
	return ifInstantiations;
    }


    /**
     * resolves collisions between bound SchemaVariables in an SVInstantiation
     *
     * @param insts the original SVInstantiations
     * @return the resolved SVInstantiations
     */
    protected static SVInstantiations resolveCollisionVarSV
	(Taclet taclet, SVInstantiations insts) {

	HashMapFromLogicVariableToSchemaVariable collMap =
	    new HashMapFromLogicVariableToSchemaVariable();
	IteratorOfEntryOfSchemaVariableAndInstantiationEntry it = 
	    insts.pairIterator();
	while (it.hasNext()) {
	    EntryOfSchemaVariableAndInstantiationEntry pair = it.next();
	    if (pair.key().isVariableSV()) {
		SchemaVariable varSV = pair.key();		
		Term value = ((TermInstantiation)pair.value()).getTerm();
		if (!collMap.containsKey((LogicVariable)value.op())) {
		    collMap.put((LogicVariable)value.op(), varSV);
		} else {
		    insts = replaceInstantiation(taclet, insts, varSV);	
		}
	    }
	}
	return insts;
    }

    /**
     * delivers the term below the (unique) quantifier of a bound
     * SchemaVariable in the given term.
     *
     * @param varSV the searched Bound Schemavariable
     * @param term the term to be searched in
     * @return the term below the given quantifier in the given term
     */
    private static Term getTermBelowQuantifier(SchemaVariable varSV, Term term) {
	for (int i=0; i<term.arity(); i++) {
	    for (int j=0; j<term.varsBoundHere(i).size(); j++) {
		if (term.varsBoundHere(i).getQuantifiableVariable(j)==varSV) {
		    return term.sub(i);
		} 
	    }
	    Term rec=getTermBelowQuantifier(varSV, term.sub(i));
	    if (rec!=null) {
		return rec;
	    }
	}
	return null;
    }

    /**
     * delivers the term below the (unique) quantifier of 
     * a bound SchemaVariable varSV in the find and if-parts of the Taclet 
     *
     * @param varSV the searched bound SchemaVariable 
     * @return the term below the given quantifier in the find and if-parts of 
     * the Taclet
     */
    private static Term getTermBelowQuantifier(Taclet taclet, SchemaVariable varSV) {
	IteratorOfConstrainedFormula it=taclet.ifSequent().iterator();
	while (it.hasNext()) {
	    Term result=getTermBelowQuantifier(varSV, it.next().formula());
	    if (result!=null) {
		return result;
	    }
	}

	if (taclet instanceof FindTaclet) {
	    return getTermBelowQuantifier(varSV, ((FindTaclet)taclet).find());
	} else	
	    return null;
    }


    /** returns true iff the instantiation of a bound SchemaVariable contains the given
    * Logicvariable 
    * @param boundVars ArrayOfQuantifiableVariable with the
    * bound SchemaVariables
    * @param x the LogicVariable that is looked for
    * @param insts the SVInstantiations where to get the necessary
    * instantiations of the bound SchemaVariables
    * @return true iff the instantiation of a Bound Schemavariable contains the given
    * Logicvariable 
    */
    private static boolean contains(ArrayOfQuantifiableVariable boundVars,
			     LogicVariable x,
			     SVInstantiations insts) {
	for (int i=0; i<boundVars.size(); i++) {
	    Term instance = (Term) insts.getInstantiation
		((SchemaVariable)boundVars.getQuantifiableVariable(i));
	    if (instance.op() == x) {
		return true;
	    } 
	}
	
	return false;
    }

    /**
     * returns a new SVInstantiations that modifies the given
     * SVInstantiations insts at the bound SchemaVariable varSV to a new LogicVariable.
     */
    protected static SVInstantiations replaceInstantiation
	(Taclet taclet, SVInstantiations insts, SchemaVariable varSV){
	Term term=getTermBelowQuantifier(taclet, varSV);
	LogicVariable newVariable = new LogicVariable 
	    (new Name(((Term)insts.getInstantiation(varSV)).op()
		      .name().toString()+"0"),
	     ((Term)insts.getInstantiation(varSV)).sort());
	// __CHANGE__ How to name the new variable? TODO
	Term newVariableTerm 
	    = TermFactory.DEFAULT.createVariableTerm(newVariable);
	return replaceInstantiation(insts, term, varSV, newVariableTerm);
    }

    /**
     * returns a new SVInstantiations that modifies the given
     * SVInstantiations insts at the bound SchemaVariable u to the Term (that is
     * a LogicVariable) y.
     */
    private static SVInstantiations replaceInstantiation
	(SVInstantiations insts, Term t,  SchemaVariable u, Term y){

	SVInstantiations result = insts;
	LogicVariable x = (LogicVariable)
	    ((Term)insts.getInstantiation(u)).op();
	if (t.op() instanceof SchemaVariable) {
	    if (!((SchemaVariable)t.op()).isVariableSV()) {
		SchemaVariable sv=(SchemaVariable)t.op();
		ClashFreeSubst cfSubst
		    = new ClashFreeSubst(x,y); 
		result = result.replace
		    (sv, 
		     cfSubst.apply((Term)insts.getInstantiation(sv)));
	    }
	} else {
	    for (int i=0; i<t.arity(); i++) {
		if (!contains(t.varsBoundHere(i), x, insts)) {	       
		    result = replaceInstantiation(result, t.sub(i),
						  u, y);
		}
	    }
		
	}

	result=result.replace(u, y);
	return result;
    }

    /** applies the specified rule at the specified position 
     * if all schema variables have been instantiated
     * @param goal the Goal at which the Taclet is applied
     * @param services the Services encapsulating all java information
     * @return list of new created goals 
     */
    public ListOfGoal execute(Goal goal, Services services) {

	if (!complete()) {	  
	    throw new IllegalStateException("Tried to apply rule \n"+taclet
					    +"\nthat is not complete.");
	}
        goal.addAppliedRuleApp(this);	
	return taclet().apply(goal, services, this);
    }    

    /** applies the specified rule at the specified position 
     * if all schema variables have been instantiated
     * and creates a new goal if the if-sequent does not match.
     * The new goal proves that the if sequent can be derived.
     * @param goal the Goal where to apply the rule
     * @param services the Services encapsulating all java information
     * @return list of new created goals 
     */
    /*
    public ListOfGoal executeForceIf(Goal goal, Services services) {
	if (!complete()) {
	    throw new IllegalStateException("Applied rule not complete.");
	}
	goal.addAppliedRuleApp(this);	
	return taclet().apply(goal, services, this, true);
    }    
    */

    /** calculate needed SchemaVariables that have not been
     * instantiated yet. This means to ignore SchemaVariables that
     * appear only in addrule-sections of Taclets
     * @return SetOfSchemaVariable that need to be instantiated but
     * are not
     */
    protected SetOfSchemaVariable calculateNonInstantiatedSV() {
	if (missingVars == null) {
	    missingVars = SetAsListOfSchemaVariable.EMPTY_SET;
	    TacletSchemaVariableCollector coll =
		new TacletSchemaVariableCollector(instantiations());
	    coll.visitWithoutAddrule(taclet());
	    IteratorOfSchemaVariable it = coll.varIterator();
	    while (it.hasNext()) {
		SchemaVariable var=it.next();
		if (!instantiations().isInstantiated(var) &&
                        !isDependingOnModifiesSV(var)) {
		    missingVars = missingVars.add(var);	
		}
	    }
	}
	return missingVars;
    }


    private NewDepOnAnonUpdates getDependingOnModifies(SchemaVariable var) {
        if ( !var.isFormulaSV () ) return null;
        
        NewDepOnAnonUpdates result = null;
        final IteratorOfVariableCondition it = taclet.getVariableConditions ();
        while ( it.hasNext () ) {
            final VariableCondition vc = it.next();
            if ( vc instanceof NewDepOnAnonUpdates
                 && ((NewDepOnAnonUpdates)vc).getUpdateSV() == var ) {
                assert result == null :
                    "" + vc + "is a duplicate dependency condition for " +
                    "schema variable " + var;
                result = (NewDepOnAnonUpdates)vc;
            }
        }

        return result;        
    }
    
    /**
     * @param sv a schema variable
     * @return true iff sv there is a variable condition of the form
     *         \newDepOnMod(modifies,sv)
     */
    public boolean isDependingOnModifiesSV(SchemaVariable sv){
        return getDependingOnModifies (sv ) != null;
    }

    
    /** Calculate needed SchemaVariables that have not been
     * instantiated yet and cannot be instantiated using
     * metavariables. This is a subset of
     * calculateNonInstantiatedSV();
     * @return SetOfSchemaVariable that need to be instantiated but
     * are not
     */
    protected SetOfSchemaVariable calculateNeededNonInstantiatedSV() {
        if ( neededMissingVars == null ) {
            IteratorOfSchemaVariable it =
                calculateNonInstantiatedSV ().iterator ();
            SchemaVariable var;
            SVInstantiations svi = instantiations ();

            neededMissingVars = SetAsListOfSchemaVariable.EMPTY_SET;

            while ( it.hasNext () ) {
                var = it.next ();
                if ( isDependingOnModifiesSV ( var ) )
                    continue;
                if ( canUseMVAPriori ( var ) ) {
                    GenericSortCondition c =
                        GenericSortCondition.forceInstantiation
                        ( ( (SortedSchemaVariable)var ).sort (), true );
                    if ( c == null )
                        continue; // then the sort is not generic
                    else {
                        try {
                            svi = svi.add ( c );
                            continue; // then the sort can be guessed
                        } catch ( GenericSortException e ) {
                            Debug.out ( "Exception thrown by class TacletApp " +
                                        "at svi.add()" );
                        }
                    }
                }

                neededMissingVars = neededMissingVars.add ( var );
            }
        }
        return neededMissingVars;
    }

    /** creates a new Tacletapp where the SchemaVariable sv is
     * instantiated with the the given Term term. Sort equality is
     * checked. If the check fails an IllegalArgumentException is
     * thrown
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    public TacletApp addCheckedInstantiation(SchemaVariable sv, 
					     Term term,
                                             Services services,
                                             boolean interesting) {

	if (sv.isVariableSV() && 
	    !(term.op() instanceof LogicVariable)) {
	    throw new IllegalInstantiationException("Could not add "+
	       "the instantiation of "+sv+" because "+
		term+" is no variable.");
	}               
              
        
        MatchConditions cond = matchConditions();
        
        if (sv instanceof SortedSchemaVariable) {
            cond = ((SortedSchemaVariable)sv).match(term, cond, services);
        } else {
            cond = sv.match(term.op(), cond, services);
        }
        	        
        if (cond == null) {
            throw new IllegalInstantiationException("Instantiation " + term + " is not matched by " + sv);
        } 
              
        cond = taclet().checkVariableConditions(sv, term, cond, services);
        
        if (cond == null) {
            throw new IllegalInstantiationException("Instantiation " + term + " of " + sv + 
                    "does not satisfy the variable conditions");
        }
        
        if (interesting) {
            cond = cond.setInstantiations(cond.getInstantiations().makeInteresting(sv));
        }
        
        return addInstantiation(cond.getInstantiations());

    }


    /**
     * returns the variables that have not yet been instantiated and
     * need to be instantiated to apply the Taclet. (These are not all
     * SchemaVariables like the one that appear only in the addrule
     * sections)
     * @return SetOfSchemaVariable with SchemaVariables that have not
     * been instantiated yet 
     */
    public SetOfSchemaVariable uninstantiatedVars() {
	return calculateNonInstantiatedSV();
    }
    
    /**
     * returns the variables that are currently uninstantiated and
     * cannot be instantiated automatically using metavariables
     * @return SetOfSchemaVariable with SchemaVariables that have not
     * been instantiated yet 
     */
    public SetOfSchemaVariable neededUninstantiatedVars() {
	return calculateNeededNonInstantiatedSV();
    }
    
    

    /**
     * @return A TacletApp with this.sufficientlyComplete() or null
     */
    public TacletApp tryToInstantiate(Goal goal, Services services) {
        final VariableNamer varNamer = services.getVariableNamer();
        final TermBuilder tb = TermBuilder.DF;
        
        TacletApp app = this;
        ListOfString proposals = SLListOfString.EMPTY_LIST;

        final IteratorOfSchemaVariable it = uninstantiatedVars().iterator();
        while (it.hasNext()) {
            SchemaVariable var = it.next();
            
            if (LoopInvariantProposer.inLoopInvariantRuleSet(taclet().ruleSets())){ 
                Object inv = LoopInvariantProposer.DEFAULT.tryToInstantiate(this, var, services);              
                if (inv instanceof Term){
                    app = app.addCheckedInstantiation(var, (Term)inv, services, true);
                } else if (inv instanceof ListOfTerm){
                    app = app.addInstantiation(var, ((ListOfTerm)inv).toArray(), true);
                } else if (inv instanceof SetOfLocationDescriptor) {
                    app = app.addInstantiation(var, ((SetOfLocationDescriptor)inv).toArray(), true);
                }   
                if (inv != null) continue;
            } 
            if(var instanceof SortedSchemaVariable) {
                SortedSchemaVariable sv = (SortedSchemaVariable)var;
                if (sv.sort() == ProgramSVSort.VARIABLE) {
                    String proposal = varNamer.getSuggestiveNameProposalForProgramVariable
                    (sv, this, goal, services, proposals);
                    ProgramElement pe = 
                        TacletInstantiationsTableModel.getProgramElement(app, proposal, sv, services);
                    app = app.addCheckedInstantiation(sv, pe, services, true);
                    proposals = proposals.append(proposal);
                } else if (sv.sort() == ProgramSVSort.LABEL) {
                    boolean nameclash;
                    do {
                        String proposal = VariableNameProposer.DEFAULT.
                            getProposal(this, sv, services, goal.node(), proposals);
                        ProgramElement pe = TacletInstantiationsTableModel.
                            getProgramElement(app, proposal, sv, services);
                        proposals = proposals.prepend(proposal);
                        try {
                            app = app.addCheckedInstantiation(sv, pe, services, true);
                        } catch (IllegalInstantiationException iie) {
                            // name clash
                            nameclash=true;
                        }
                        nameclash=false;
                    } while (nameclash);                    
                } else if ( sv.isSkolemTermSV () ) {
                    // if the sort of the schema variable is generic,
                    // ensure that it is instantiated
                    app = forceGenericSortInstantiation(app, sv);
                    if ( app == null ) return null;
    
                    String proposal = VariableNameProposer.DEFAULT
                        .getProposal(app, sv, services, goal.node(), null);
                    app = app.createSkolemConstant ( proposal,
    						        sv,
    						        true, services );
                } else if ( sv.isVariableSV () ) {
                    // if the sort of the schema variable is generic,
                    // ensure that it is instantiated
                    app = forceGenericSortInstantiation ( app, sv );
                    if ( app == null ) return null;
                    
                    String proposal = VariableNameProposer.DEFAULT
                    .getProposal( this, sv, services, goal.node(), null );
                    final LogicVariable v = new LogicVariable ( new Name ( proposal ),
                            getRealSort ( sv, services ) );                
                    app = app.addCheckedInstantiation ( sv, tb.var(v), services, true );
                } else if ( !( sv.isTermSV () && canUseMVAPriori ( sv ) ) ) {
                    return null;
                }
            }      
        }
        
        if (app != this) {
            final MatchConditions appMC = 
                app.taclet().checkConditions(app.matchConditions(), services);
            if (appMC == null) {              
                return null;
            } else {
                app = app.setMatchConditions(appMC);
            }
        }
              
        if (!app.sufficientlyComplete()) {         
            return null;
        }
        return app;
    }
    
    /**
     * If the sort of the given schema variable is generic, add a
     * condition to the instantiations of the given taclet app that
     * requires the sort to be instantiated
     * @return the new taclet app, or <code>null</code> if the sort of
     * <code>sv</code> is generic and cannot be instantiated (at least
     * at the time)
     */
    private static TacletApp
	forceGenericSortInstantiation (TacletApp app,
				       SortedSchemaVariable sv) {
        final GenericSortCondition c =
            GenericSortCondition.forceInstantiation ( sv.sort (), false );
        if ( c != null ) {
            try {
                app = app.setInstantiation ( app.instantiations ().add ( c ) );
            } catch ( GenericSortException e ) {
                return null;
            }
        }
        return app;
    }

    /**
     * Examine all schema variables of the taclet that are currently
     * not instantiated, and for each one whose sort is generic add a
     * condition to the instantiations object <code>insts</code> that
     * requires this sort to be instantiated
     * @return the instantiations object after adding all the
     * conditions, or <code>null</code> if any of the generic sorts
     * found cannot be instantiated (at least at the time)
     */
    private SVInstantiations forceGenericSortInstantiations (SVInstantiations insts) {
        final IteratorOfSchemaVariable it  = uninstantiatedVars().iterator ();

	    // force all generic sorts to be instantiated
	    try {
		while ( it.hasNext () ) {
		    final SchemaVariable sv = it.next ();
		    final GenericSortCondition c =
		        GenericSortCondition.forceInstantiation
		                ( ( (SortedSchemaVariable)sv ).sort (), true );
		    if ( c != null ) 			                      
		        insts = insts.add ( c );                                                                        
		}
	    } catch ( GenericSortException e ) {
		Debug.fail ( "TacletApp cannot be made complete" );		
	    }
        return insts;
    }

    /**
     * Make the instantiation complete using metavariables and convert plain
     * instantiations to metavariables and user constraint entries if possible.
     * Pre-condition: this.sufficientlyComplete()
     */
    public TacletApp instantiateWithMV ( Goal p_goal ) {

	Debug.assertTrue ( this.sufficientlyComplete (),
			   "TacletApp cannot be made complete" );

	final Proof proof = p_goal.proof ();
    
        Services services = proof.getServices();
        
	SVInstantiations  insts   = instantiations   ();
	SetOfMetavariable newVars = newMetavariables ();
	Constraint        constr = constraint ();

	if ( newVars != SetAsListOfMetavariable.EMPTY_SET ) {
            // Replace temporary metavariables that were introduced
            // when matching the taclet with real MVs
            final IteratorOfMetavariable mvIt = newVars.iterator ();
            newVars = SetAsListOfMetavariable.EMPTY_SET;
            SetOfMetavariable removeVars = SetAsListOfMetavariable.EMPTY_SET; 
            Constraint replaceC = Constraint.BOTTOM;            
            while ( mvIt.hasNext () ) {
                final Metavariable mv = mvIt.next();
                if ( mv.isTemporaryVariable() ) {
                    String s = "" + mv.name ();
                    s += "_"+MetavariableDeliverer.mv_Counter(s, p_goal);
                    final Metavariable newMV = proof.getMetavariableDeliverer ()
                        .createNewVariable (s , mv.sort () );
                    newVars = newVars.add ( newMV );
                    removeVars = removeVars.add ( mv );
                    final Term newT = TermFactory.DEFAULT.createFunctionTerm ( newMV );
                    final Term t = TermFactory.DEFAULT.createFunctionTerm ( mv );
                    replaceC = replaceC.unify ( t, newT, services );
                } else
                    newVars = newVars.add ( mv );
            }
            
            if ( !replaceC.isBottom () ) {
                constr = removeTemporaryMVsFromConstraint ( constr,
                                                            removeVars,
                                                            replaceC,
                                                            services);
                insts = removeTemporaryMVsFromInstantiations ( insts, replaceC );
            }
        }
	
	// Replace plain instantiations of termSV

	final IteratorOfEntryOfSchemaVariableAndInstantiationEntry it    =
	    insts.pairIterator ();

	while ( it.hasNext () ) {
	    final EntryOfSchemaVariableAndInstantiationEntry entry = it.next ();
	    final SchemaVariable sv = entry.key ();

	    if ( introduceMVFor ( entry, sv ) ) {
                final Metavariable mv = getMVFor ( sv, proof, p_goal, insts );
                newVars = newVars.add ( mv );
                final Term t = TermFactory.DEFAULT.createFunctionTerm ( mv );
                proof.getUserConstraint ().addEquality ( t,
                             ( (TermInstantiation)entry.value () ).getTerm () );
                insts = insts.replace ( sv, t );
            }
        }

	return handleUninstantiatedSVs(proof, p_goal, insts, constr, newVars);
    }


    /**
     * Replace temporary metavariables (that were introduced when
     * matching the taclet parts) within <code>insts</code> with
     * definite metavariables
     * @param replaceC a constraint that unifies each temporary
     * metavariable with the corresponding definite metavariable
     */
    private static SVInstantiations
	removeTemporaryMVsFromInstantiations (SVInstantiations insts,
					      Constraint replaceC) {
        final IteratorOfEntryOfSchemaVariableAndInstantiationEntry it =
            insts.pairIterator ();

        while ( it.hasNext () ) {
            final EntryOfSchemaVariableAndInstantiationEntry entry = it.next ();
            final SchemaVariable sv = entry.key ();

            if ( sv.isFormulaSV() || sv.isTermSV() ) {
                final Object inst = entry.value().getInstantiation ();
                // NB: this only works because of the implementation of
                // <code>Metavariable.compareTo</code>, in which temporary MVs
                // are regarded as greater than normal MVs
                final SyntacticalReplaceVisitor srVisitor =
                    new SyntacticalReplaceVisitor ( replaceC );
                ( (Term)inst ).execPostOrder ( srVisitor );
                insts = insts.replace ( sv, srVisitor.getTerm () );
            }
        }
        return insts;
    }

    /**
     * Replace temporary metavariables (that were introduced when
     * matching the taclet parts) within <code>constr</code> with
     * definite metavariables
     * @param removeVars the set of temporary metavariables to be
     * removed
     * @param replaceC a constraint that unifies each temporary
     * metavariable with the corresponding definite metavariable
     * @param services the Services 
     */
    private static Constraint
	removeTemporaryMVsFromConstraint (Constraint constr,
					  SetOfMetavariable removeVars,
					  Constraint replaceC,
                                          Services services) {
        // that's tricky ...
        constr = constr.join ( replaceC, services );
        return constr.removeVariables ( removeVars );
    }

    /**
     * @return true iff it is possible to use a metavariable to make
     * the given instantiation indirect, i.e. to instantiate the
     * schema variable with a metavariable instead of a term, and to
     * add the real instantiation to the user constraint
     */
    private boolean introduceMVFor (EntryOfSchemaVariableAndInstantiationEntry entry,
                                    SchemaVariable sv) {
        return sv.isTermSV () && !sv.isListSV()
               && !taclet ().getIfFindVariables ().contains ( sv )
               && canUseMVAPosteriori ( sv,
                            ( (TermInstantiation)entry.value () ).getTerm () );
    }

    /**
     * Instantiate all uninstantiated schema variables with
     * metavariables; it is assumed that this is possible (currently
     * checked using an assertion)
     * @return a new taclet app in which all schema variables are
     * instantiated
     */
    private TacletApp handleUninstantiatedSVs (Proof proof,
                                               Goal goal,
                                               SVInstantiations insts,
                                               Constraint constr,
                                               SetOfMetavariable newVars) {
        insts = forceGenericSortInstantiations ( insts );

        final IteratorOfSchemaVariable it = uninstantiatedVars ().iterator ();
        while ( it.hasNext () ) {
            final SchemaVariable sv = it.next ();
            if (isDependingOnModifiesSV(sv))
                continue;
            Debug.assertTrue ( canUseMVAPriori ( sv ),
                               "Should be able to instantiate "
                               + sv
                               + " using metavariables, but am not" );
            
            final Metavariable mv = getMVFor(sv, proof, goal, insts);
            newVars = newVars.add ( mv );
            final Term t = TermFactory.DEFAULT.createFunctionTerm ( mv );
            insts = insts.add ( sv, t );
            NameSV nameSV = new NameSV(new Name(NameSV.MV_NAME_PREFIX+sv.name()));
            insts = insts.addInteresting (nameSV, mv.name());
        }

        return setMatchConditions ( new MatchConditions ( insts,
                                                          constr,
                                                          newVars,
                                                          RenameTable.EMPTY_TABLE ) );
    }

    /**
     * Create a Metavariable the given SchemaVariable can be
     * instantiated with
     * @return an appropriate mv, or null if for some reason the
     * creation failed
     */
    private Metavariable getMVFor (SchemaVariable sv,
                                   Proof proof,
                                   Goal goal,
                                   SVInstantiations insts) {
        final Sort realSort = insts.getGenericSortInstantiations().
            getRealSort(sv, proof.getServices());
        SchemaVariable nameSV = insts.lookupVar(
            new Name(NameSV.MV_NAME_PREFIX+sv.name()));
        Name proposal = (Name) insts.getInstantiation(nameSV);
        String s = (proposal==null) ? "" : proposal.toString();
        return getMVFor ( sv, realSort, proof, goal, s );
    }

    /**
     * Create a Metavariable the given SchemaVariable can be
     * instantiated with
     * @return an appropriate mv, or null if for some reason the
     * creation failed
     */
    private Metavariable getMVFor ( SchemaVariable p_sv,
				    Sort           p_sort,
				    Proof          p_proof,
                                    Goal goal,
                                    String nameProposal ) {
        if ("".equals(nameProposal)) {
            nameProposal = TacletInstantiationsTableModel
	      .getNameProposalForMetavariable ( goal, this, p_sv );
        }
	return p_proof.getMetavariableDeliverer().
            createNewVariable(nameProposal, p_sort);
    }


    /**
     * @param services the Services class allowing access to the type model
     * @return p_s iff p_s is not a generic sort, the concrete sort
     * p_s is instantiated with currently otherwise 
     * @throws GenericSortException iff p_s is a generic sort which is
     * not yet instantiated
     */
    public Sort getRealSort ( SchemaVariable p_sv, Services services )  {
	return instantiations ().getGenericSortInstantiations ()
	    .getRealSort ( p_sv, services );
    }

    /**
     * Create a new constant named "instantiation" and instantiate
     * "sv" with. This constant will later (by
     * "createSkolemFunctions") be replaced by a function having
     * the occurring metavariables as arguments
     * @param services the Services class allowing access to the type model
     */
    public TacletApp createSkolemConstant ( String         instantiation,
					       SchemaVariable sv,
					       boolean        interesting, 
                                               Services services ) {
	return createSkolemConstant ( instantiation,
					 sv,
					 getRealSort ( sv, services ),
					 interesting );
    }
    
    public TacletApp createSkolemConstant ( String         instantiation,
					       SchemaVariable sv,
					       Sort           sort,
					       boolean        interesting ) {
	Function c = new RigidFunction ( new Name ( instantiation ),
				    sort,
				    new Sort [0] );
	return addInstantiation ( sv,
				  TermFactory.DEFAULT.createFunctionTerm ( c ),
				  interesting );
    }
    

    /**
     * Create skolem functions (for variables declared via "\\new(c,
     * \\dependingOn(phi))" or via "\\new(upd, \\dependingOnMod(#modifiers))")
     * to replace previously created constants with
     */
    public TacletApp createSkolemFunctions ( Namespace p_func_ns, Services services ) {
        SVInstantiations insts = instantiations ();

        final IteratorOfSchemaVariable svIt = insts.svIterator ();        
        while ( svIt.hasNext () )
            insts = createTermSkolemFunctions ( svIt.next (), insts, p_func_ns );
        
        final IteratorOfVariableCondition vcIt = taclet.getVariableConditions ();
        while ( vcIt.hasNext () ) {
            final VariableCondition vc = vcIt.next();
            if ( vc instanceof NewDepOnAnonUpdates )
                insts = createModifiesSkolemFunctions((NewDepOnAnonUpdates)vc,
                                                      insts, services);
        }
        
        if ( insts == instantiations () ) return this;
        return setInstantiation ( insts );
    }

    /**
     * Instantiate a SkolemTermSV
     */
    private SVInstantiations createTermSkolemFunctions(SchemaVariable depSV,
                                                       SVInstantiations insts,
                                                       Namespace p_func_ns) {
        if ( !depSV.isSkolemTermSV () ) return insts;

        final Term tempDepVar = (Term)insts.getInstantiation ( depSV );

        Debug.assertTrue ( tempDepVar != null,
                           "Name for skolemterm variable missing" );

        return createSkolemFunction ( insts, p_func_ns, depSV, tempDepVar,
                                      determineArgMVs ( insts, depSV ) );
    }
        
    /**
     * Instantiate a schemavariable for an anonymous update (FormulaSV)
     */
    private SVInstantiations
        createModifiesSkolemFunctions(NewDepOnAnonUpdates cond,
                                      SVInstantiations insts,
                                      Services services) {
        final SchemaVariable modifies = cond.getModifiesSV ();
        final SchemaVariable updateSV = cond.getUpdateSV ();
        
        if (insts.isInstantiated ( updateSV )) {
            System.err.println(
                "Modifies skolem functions already created - ignoring.");
            return insts;
        }
        
        final ListOfObject locationList =
            (ListOfObject)insts.getInstantiation ( modifies );
        final AnonymisingUpdateFactory auf =
            new AnonymisingUpdateFactory
            ( new UpdateFactory ( services, new UpdateSimplifier () ) );
        final Term[] mvArgs = toTermArray ( determineArgMVs ( insts, updateSV ) );
        return insts.add ( updateSV,
                           auf.createAnonymisingUpdateAsFor
                                  ( toLocationDescriptorArray ( locationList ),
                                    mvArgs, services ) );
    }
    
    private static LocationDescriptor[]
               toLocationDescriptorArray(ListOfObject locationList) {
        final LocationDescriptor[] locations =
            new LocationDescriptor [locationList.size ()];

        for ( int i = 0; i < locations.length; i++ ) {
            locations[i] = (LocationDescriptor)locationList.head ();
            locationList = locationList.tail ();
        }
        return locations;
    }

    
    /**
     * Determine the metavariables that have to be added as arguments to newly
     * created skolem symbols (as basis of the occurs check)
     */
    private SetOfMetavariable determineArgMVs (SVInstantiations insts,
                                               SchemaVariable depSV) {
        return
            determineExplicitArgMVs ( insts, depSV )
            .union ( determineArgMVsFromUpdate ( insts ) );
    }

    private SetOfMetavariable determineExplicitArgMVs(SVInstantiations insts,
                                                      SchemaVariable depSV) {
        final IteratorOfNewDependingOn it = taclet ().varsNewDependingOn ();
        SetOfMetavariable mvs = SetAsListOfMetavariable.EMPTY_SET;
        while ( it.hasNext () ) {
            final NewDependingOn newDepOn = it.next ();
            if ( depSV != newDepOn.first () ) continue;
            
            final Term dominantTerm =
                (Term)insts.getInstantiation ( newDepOn.second () );

            assert dominantTerm != null :
                "Variable depends on uninstantiated variable";
            mvs = mvs.union ( dominantTerm.metaVars () );                
        }
        return mvs;
    }

    private SetOfMetavariable determineArgMVsFromUpdate(SVInstantiations insts) {
        final IteratorOfUpdatePair it = insts.getUpdateContext ().iterator ();
        SetOfMetavariable mvs = SetAsListOfMetavariable.EMPTY_SET;
        while ( it.hasNext () ) {
            final UpdatePair pair = it.next ();
            final IUpdateOperator upOp = pair.updateOperator ();
            for ( int i = 0; i != upOp.arity (); ++i ) {
                if ( i == upOp.targetPos () ) continue;
                mvs = mvs.union ( pair.sub ( i ).metaVars () );
            }
        }
        return mvs;
    }

    
    private SVInstantiations createSkolemFunction (SVInstantiations insts,
                                                   Namespace p_func_ns,
                                                   SchemaVariable depSV,
                                                   Term tempDepVar,
                                                   SetOfMetavariable mvs) {
        if ( mvs == SetAsListOfMetavariable.EMPTY_SET ) {
            // if the term contains no metavariables, we just use the
            // (nullary) constant <code>tempDepVar</code> as skolem symbol
            p_func_ns.add ( tempDepVar.op () );
            return insts;
        }

        final Term[] argTerms = toTermArray ( mvs );
        final Function skolemFunc = new RigidFunction ( tempDepVar.op ().name (),
                                                        tempDepVar.sort (),
                                                        extractSorts ( argTerms ) );
        final Term skolemTerm =
            TermFactory.DEFAULT.createFunctionTerm ( skolemFunc, argTerms );

        p_func_ns.add ( skolemFunc );
        return insts.replace ( depSV, skolemTerm );
    }

    private Term[] toTermArray(SetOfMetavariable mvs) {
        final Metavariable[] mvArray = mvs.toArray ();
        Arrays.sort ( mvArray );
        
        // Create function with correct arguments
        final Term[] argTerms = new Term [mvArray.length];
        
        for ( int i = 0; i != mvArray.length; ++i )
            argTerms[i] = TermFactory.DEFAULT.createFunctionTerm ( mvArray[i] );

        return argTerms;
    }

    private Sort[] extractSorts(Term[] argTerms) {
        final Sort[] argSorts = new Sort [argTerms.length];
        for ( int i = 0; i != argTerms.length; ++i )
            argSorts[i] = argTerms[i].sort ();
        return argSorts;
    }

    
    /** adds a new instantiation to this TacletApp 
     * @param sv the SchemaVariable to be instantiated
     * @param term the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    public abstract TacletApp addInstantiation(SchemaVariable sv, Term term,
                                               boolean interesting);
    

    public abstract TacletApp addInstantiation(SchemaVariable sv, Object[] list,
            boolean interesting);
    
    
    /** 
     * adds a new instantiation to this TacletApp. This method does not 
     * check (beside some very rudimentary tests) if the instantiation is possible.
     * If you cannot guarantee that adding the entry <code>(sv, pe)</code> will 
     * result in a valid taclet instantiation, you have to use 
     * {@link #addCheckedInstantiation(SchemaVariable, ProgramElement, Services, boolean)}
     * instead
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SV is instantiated with
     * @param interesting a boolean marking if the instantiation of this
     *  sv needs to be saved for later proof loading (<code>interesting==true</code>)
     *  or if it can be derived deterministically (e.g. by matching) 
     *  (<code>interesting==false</code>)
     * @return a new taclet application equal to this one but including the
     * newly added instantiation entry <code>(sv, pe)</code> 
     */
    public abstract TacletApp addInstantiation(SchemaVariable sv, 
					       ProgramElement pe,
                                               boolean interesting);

    
    /** 
     * checks if the instantiation of <code>sv</code> with <code>pe</code>
     * is possible. If the resulting instantiation is valid a new taclet application
     * with an extended instantiation mapping is created and returned. Otherwise an
     * exception is thrown.   
     * @param sv the SchemaVariable to be instantiated
     * @param pe the ProgramElement the SV is instantiated with
     * @param services the Services
     * @param interesting a boolean marking if the instantiation of this
     *  sv needs to be saved for later proof loading (<code>interesting==true</code>)
     *  or if it can be derived deterministically (e.g. by matching) 
     *  (<code>interesting==false</code>)
     * @return a new taclet application equal to this one but including the
     * newly added instantiation entry <code>(sv, pe)</code>, if the
     * instantiation results in a valid taclet application otherwise an exception is thrown
     * @throws IllegalInstantiationException exception thrown if 
     *  <code>sv</code> cannot be instantiated with <code>pe</code> no matter if in general
     *   or due to side conditions posed by this particular application 
     *  
     */
    public TacletApp addCheckedInstantiation
        (SchemaVariable sv, ProgramElement pe, 
                Services services, boolean interesting) {
      
        MatchConditions cond = matchConditions();
        
        if (sv instanceof ProgramSV) {
            cond = ((ProgramSV)sv).match(pe, cond, services);
        } else {
            throw new IllegalInstantiationException("Cannot match program element '"+ pe +
                    "'("+(pe == null ? null : pe.getClass().getName())+") to non program sv " + sv);
        }
                               
        if (cond == null) {           
            throw new IllegalInstantiationException("Instantiation " + pe + 
                    "(" + (pe == null ? null : pe.getClass().getName())+
                    ") is not matched by " + sv);
        }
        
        cond = taclet().checkConditions(cond, services);
        
        if (cond == null) {
            throw new IllegalInstantiationException("Instantiation " + pe + " of " + sv + 
                    "does not satisfy variable conditions");
        }
        
        if (interesting) {
            cond = cond.setInstantiations(cond.getInstantiations().makeInteresting(sv));
        }
        
        return addInstantiation(cond.getInstantiations());
             
    }

    public TacletApp addInstantiation(SchemaVariable sv, Name name) {
        return 
	    addInstantiation(SVInstantiations.
			     EMPTY_SVINSTANTIATIONS.addInteresting(sv, name));
    }


    /**
     * creates a new Taclet application containing all the
     * instantiations given 
     * by the SVInstantiations
     * @param svi the SVInstantiations whose entries are the needed
     * instantiations 
     * @return the new Taclet application
     */
    public abstract TacletApp addInstantiation(SVInstantiations svi);


    /**
     * creates a new Taclet application containing all the
     * instantiations given 
     * by the SVInstantiations and forget the old ones
     * @param svi the SVInstantiations whose entries are the needed
     * instantiations 
     * @return the new Taclet application
     */
    protected abstract TacletApp setInstantiation(SVInstantiations svi);


    /**
     * creates a new Taclet application containing all the
     * instantiations, constraints and new metavariables given 
     * by the mc object and forget the old ones
     */
    protected abstract TacletApp setMatchConditions ( MatchConditions mc );


    /**
     * creates a new Taclet application containing all the
     * instantiations, constraints, new metavariables and if formula
     * instantiations given and forget the old ones
     */
    protected abstract TacletApp
	setAllInstantiations ( MatchConditions              mc,
			       ListOfIfFormulaInstantiation ifInstantiations );


    /**
     * Creates a new Taclet application by matching the given formulas
     * against the formulas of the if sequent, adding SV
     * instantiations, constraints and metavariables as needed. This
     * will fail if the if formulas have already been instantiated.
     */
    public TacletApp setIfFormulaInstantiations
	( ListOfIfFormulaInstantiation p_list,
	  Services                     p_services,
	  Constraint                   p_userConstraint ) {
	assert p_list != null && ifInstsCorrectSize ( taclet, p_list ) &&
	    ifInstantiations == null :
	    "If instantiations list has wrong size or is null " +
	    "or the if formulas have already been instantiated";
		
	MatchConditions  mc = taclet ().matchIf ( p_list.iterator (),
						  matchConditions (),
						  p_services,
						  p_userConstraint );
	
	return mc == null ? null : setAllInstantiations ( mc, p_list );
    }


    /**
     * Find all possible instantiations of the if sequent formulas
     * within the sequent "p_seq".
     * @return a list of tacletapps with the found if formula
     * instantiations
     */
    public ListOfTacletApp
	findIfFormulaInstantiations ( Sequent     p_seq,
	                              Services    p_services,
				      Constraint  p_userConstraint ) {
	
	Debug.assertTrue ( ifInstantiations == null,
			   "The if formulas have already been instantiated" );

	if ( taclet ().ifSequent () == Sequent.EMPTY_SEQUENT )
	    return SLListOfTacletApp.EMPTY_LIST.prepend ( this );        
        
	return
	    findIfFormulaInstantiationsHelp
	    ( createSemisequentList ( taclet ().ifSequent ()  // Matching starting
				      .succedent () ),    // with the last formula
	      createSemisequentList ( taclet ().ifSequent ()
				      .antecedent () ),
	      IfFormulaInstSeq.createList(p_seq, false),
	      IfFormulaInstSeq.createList(p_seq, true),
	      SLListOfIfFormulaInstantiation.EMPTY_LIST,
	      matchConditions (),
	      p_services,
	      p_userConstraint );
	
    }

    
    /**
     * Recursive function for matching the remaining tail of an if sequent
     * @param p_ifSeqTail tail of the current semisequent as list
     * @param p_ifSeqTail2nd the following semisequent
     * (i.e. antecedent) or null
     * @param p_toMatch list of the formulas to match the current if
     * semisequent formulas with
     * @param p_toMatch2nd list of the formulas of the antecedent
     * @param p_matchCond match conditions until now, i.e. after
     * matching the first formulas of the if sequent
     */
    private ListOfTacletApp findIfFormulaInstantiationsHelp
	( ListOfConstrainedFormula      p_ifSeqTail,
	  ListOfConstrainedFormula      p_ifSeqTail2nd,
	  ListOfIfFormulaInstantiation  p_toMatch,
	  ListOfIfFormulaInstantiation  p_toMatch2nd,
	  ListOfIfFormulaInstantiation  p_alreadyMatched,
	  MatchConditions               p_matchCond,
	  Services                      p_services,
	  Constraint                    p_userConstraint ) {

	while ( p_ifSeqTail == SLListOfConstrainedFormula.EMPTY_LIST ) {
	    if ( p_ifSeqTail2nd == null ) {
		// All formulas have been matched, collect the results
		TacletApp res = setAllInstantiations ( p_matchCond,
						       p_alreadyMatched );
		if ( res != null )
		    return SLListOfTacletApp.EMPTY_LIST.prepend ( res );
		return SLListOfTacletApp.EMPTY_LIST;
	    } else {
		// Change from succedent to antecedent
		p_ifSeqTail    = p_ifSeqTail2nd;
		p_ifSeqTail2nd = null;
		p_toMatch      = p_toMatch2nd;
	    }
	}

	// Match the current formula
	IfMatchResult mr        = taclet ().matchIf ( p_toMatch.iterator (),
						      p_ifSeqTail.head ().formula (),
						      p_matchCond,
						      p_services,
						      p_userConstraint );

	// For each matching formula call the method again to match
	// the remaining terms
	ListOfTacletApp                  res    = SLListOfTacletApp.EMPTY_LIST;
	IteratorOfIfFormulaInstantiation itCand = mr.getFormulas        ().iterator ();
	IteratorOfMatchConditions        itMC   = mr.getMatchConditions ().iterator ();
	p_ifSeqTail                             = p_ifSeqTail.tail ();
	while ( itCand.hasNext () ) {
	    res = res.prepend
		( findIfFormulaInstantiationsHelp ( p_ifSeqTail,
						    p_ifSeqTail2nd,
						    p_toMatch,
						    p_toMatch2nd,
						    p_alreadyMatched
						    .prepend ( itCand.next () ),
						    itMC.next (),
						    p_services,
						    p_userConstraint ) );
	}

	return res;
    }

    private ListOfConstrainedFormula createSemisequentList ( Semisequent p_ss ) {
	ListOfConstrainedFormula res = SLListOfConstrainedFormula.EMPTY_LIST;

	IteratorOfConstrainedFormula it  = p_ss.iterator ();
	while ( it.hasNext () )
	    res = res.prepend ( it.next () );

	return res;	
    }


    /**
     * returns a new PosTacletApp that is equal to this TacletApp except
     * that the position is set to the given PosInOccurrence
     * @param pos the PosInOccurrence of the newl created PosTacletApp
     * @return the new TacletApp
     */
    public PosTacletApp setPosInOccurrence(PosInOccurrence pos) {
	if (taclet() instanceof NoFindTaclet) {
	    throw new IllegalStateException("Cannot add position to an taclet"
					    +" without find");
	}
	return PosTacletApp.createPosTacletApp((FindTaclet)taclet      (), 
					       instantiations          (),
					       constraint              (),
					       newMetavariables        (),
					       ifFormulaInstantiations (),
					       pos);
    }


    /** returns true iff all necessary informations are collected, so
     * that the Taclet can be applied.
     * @return true iff all necessary informations are collected, so
     * that the Taclet can be applied.
     */
    public abstract boolean complete();


    /**
     * @return true iff the taclet instantiation can be made complete
     * using metavariables
     */
    public abstract boolean sufficientlyComplete();


    /**
     * @return true iff the SV instantiations can be made complete
     * using metavariables
     */
    public boolean instsSufficientlyComplete() {
	return neededUninstantiatedVars () == SetAsListOfSchemaVariable.EMPTY_SET;
    }


    /**
     * @return true iff the if instantiation list is not null or no if
     * sequent is needed
     */
    public boolean ifInstsComplete() {
	return ifInstantiations != null ||
	    ( taclet ().ifSequent () == Sequent.EMPTY_SEQUENT );
    }


    /**
     * returns the PositionInOccurrence (representing a ConstrainedFormula and
     * a position in the corresponding formula)
     * @return the PosInOccurrence
     */
    public abstract PosInOccurrence posInOccurrence();


    /** compares the given Object with this one and returns true iff both are
     * from type TacletApp with equal taclets, instantiations and positions.
     */
    public boolean equals(Object o) {
	if (o==this) return true;
	if (!(o instanceof TacletApp)) return false;
	TacletApp s=(TacletApp)o;
	return (s.taclet().equals(taclet()) 
		&& s.instantiations().equals(instantiations()));
    }

    public int hashCode() {
        int result = 17;
        result = 37 * result + taclet.hashCode();
        result = 37 * result + instantiations.hashCode();
        return result;
    }
    
    public String toString() {
	return "Application of Taclet " +taclet()+ " with "
	    +instantiations() + " and " + ifFormulaInstantiations();
    }


    /**
     * checks if there are name conflicts (i.e. there are
     * two matched bound SchemaVariable that are matched to variables with an
     * equal name); if yes a new TacletApp is returned that equals this
     * TacletApp except that the name conflict is resolved by replacing the
     * instantiation of one of the conflict-causing SchemaVariables by a 
     * bound SchemaVariable with a new name; 
     * if the check is negative, the same TacletApp is returned.
     *
     * @return a conflict resolved TacletApp, remainder equal to this TacletApp
     */
    public TacletApp prepareUserInstantiation() {
	TacletApp result = this;
	SchemaVariable varSV = varSVNameConflict();
	while (varSV!=null) {
	    result = setInstantiation(replaceInstantiation
				    (taclet, result.instantiations(), varSV));
	    varSV = result.varSVNameConflict();
	}
	return result;
    }

    protected abstract SetOfQuantifiableVariable contextVars(SchemaVariable sv);

    /**
     * creates a new variable namespace by adding names of the instantiations
     * of the schema variables in the context of the given schema
     * variable and (if the TacletApp's prefix has the context flag set)
     * by adding names of the logic variables of the context.
     *
     * @param sv the schema variable to be considered
     * @param var_ns the old variable namespace
     * @return the new created variable namespace
     */
    public Namespace extendVarNamespaceForSV(Namespace var_ns, 
					     SchemaVariable sv) {
	Namespace ns=new Namespace(var_ns);
        IteratorOfSchemaVariable it=taclet().getPrefix(sv).prefix().iterator();
	while (it.hasNext()) {
	    LogicVariable var = (LogicVariable) 
		((Term)instantiations().getInstantiation(it.next())).op();
	    ns.add(var);
	}
	if (taclet().getPrefix(sv).context()) {	    
	    IteratorOfQuantifiableVariable lit
		= contextVars(sv).iterator();
	    while (lit.hasNext()) {
		ns.add(lit.next());
	    }
	}
	return ns;
    }

    /**
     * create a new function namespace by adding all newly instantiated 
     * skolem symbols to a new namespace.
     * 
     * @author mulbrich
     * @param func_ns the original function namespace
     * @return the new function namespace that bases on the original one
     */
    public Namespace extendedFunctionNameSpace(Namespace func_ns) {
        Namespace ns = new Namespace(func_ns);
        IteratorOfSchemaVariable it = instantiations.svIterator();
        while(it.hasNext()) {
            SchemaVariable sv = it.next();
            if(sv.isSkolemTermSV()) {            
                Term inst = (Term) instantiations.getInstantiation(sv);
                ns.addSafely(inst.op());
            }
        }
        return ns;
    }

    /**
     * returns the bound SchemaVariable that causes a name conflict (i.e. there are
     * two matched bound SchemaVariables that are matched to variables with an
     * equal name, the returned SchemaVariable is (an arbitrary) one of these
     * SchemaVariables) or null if there is no such conflict
     *
     * @return null iff there is no conflict and one of the
     * conflict-causing bound SchemaVariables
     */
    public SchemaVariable varSVNameConflict() {
	IteratorOfSchemaVariable svIt=uninstantiatedVars().iterator();
	while (svIt.hasNext()) { 
	    SchemaVariable sv=svIt.next();
	    if (sv.isTermSV() || sv.isFormulaSV()) {
		TacletPrefix prefix=taclet().getPrefix(sv);
		HashSet names=new HashSet();	    
		if (prefix.context()) {
		    IteratorOfQuantifiableVariable contextIt
			= contextVars(sv).iterator();
		    while (contextIt.hasNext()) {
			names.add(contextIt.next().name());
		    }
		}
		IteratorOfSchemaVariable varSVIt=prefix.iterator();
		while(varSVIt.hasNext()) {
		    SchemaVariable varSV=varSVIt.next();
		    Term inst = (Term)
			instantiations().getInstantiation(varSV);
		    if (inst!=null) {
			Name name = inst.op().name();
			if (!names.contains(name)) {
			    names.add(name);
			} else {
			    return varSV;
			}
		    }
		}
	    }
	}
	return null;
    }


    /**
     * For a given SV of the taclet decide a priori whether an
     * instantiation via metavariable is possible
     * @return true iff p_var is a termSV with empty prefix
     */
    public boolean canUseMVAPriori ( SchemaVariable p_var ) {
	if ( !p_var.isTermSV () ||
	     fixedVars.contains ( p_var ) )
	    return false;
	else {
	    TacletPrefix prefix = taclet ().getPrefix ( p_var );
	    return (prefix.prefix ().size () == 0 && !prefix.context ());
	}
    }


    /**
     * For a given SV of the taclet decide a posteriori whether an
     * instantiation via metavariable is possible
     * @param p_term Term to instantiate the schemavariable with
     */
    protected boolean canUseMVAPosteriori ( SchemaVariable p_var, Term p_term ) {
        // disabled
        return false;
//	return canUseMVAPriori ( p_var ) && p_term.isRigid ();
    }    


    /**
     * @return true iff the list of if instantiations has the correct
     * size or is null
     */
    protected static boolean ifInstsCorrectSize ( Taclet                       p_taclet,
						  ListOfIfFormulaInstantiation p_list ) {        
	return p_list == null ||
	    p_list.size () == ( p_taclet.ifSequent ().antecedent ().size () +
				p_taclet.ifSequent ().succedent  ().size () );
    }

    /**
     * @return true iff the Taclet may be applied for the
     * given mode (interactive/non-interactive, activated rule sets)
     */
    public boolean admissible(boolean       interactive,
			      ListOfRuleSet ruleSets) {
	return taclet ().admissible (interactive, ruleSets);
    }

    /** checks if the variable conditions of type 'x not free in y' are
     * hold by the found instantiations. The variable conditions is used
     * implicit in the prefix. (Used to calculate the prefix)
     * @param taclet the Taclet that is tried to be instantiated. A match for the
     * find (or/and if) has been found.
     * @param instantiations the SVInstantiations so that the find(if)
     * expression matches
     * @param pos the PosInOccurrence where the Taclet is applied
     * @return true iff all variable conditions x not free in y are hold
     */
    public static boolean checkVarCondNotFreeIn
	( Taclet taclet, SVInstantiations instantiations, PosInOccurrence pos ) {
        
        IteratorOfSchemaVariable it = instantiations.svIterator();
	while (it.hasNext()) {
	    SchemaVariable sv = it.next();
	    if (sv.isTermSV() || sv.isFormulaSV()) {
		if (!((Term)instantiations.getInstantiation(sv)).
		    freeVars().subset(boundAtOccurrenceSet
				      (taclet.getPrefix(sv), 
				       instantiations, pos))) {
    	    
		    return false;
		}
	    }
	}
	return true;
    }

    /** collects all bound vars that are bound above the subterm described by
     * the given term position information
     * @param pos the PosInOccurrence describing a subterm in Term
     * @return a set of logic variables that are bound above the specified
     * subterm 
     */
    protected static SetOfQuantifiableVariable collectBoundVarsAbove
	( PosInOccurrence pos ) {
	SetOfQuantifiableVariable result = SetAsListOfQuantifiableVariable.EMPTY_SET;
    
	PIOPathIterator             it   = pos.iterator ();
	int                         i;
	ArrayOfQuantifiableVariable vars;
    
	while ( ( i = it.next () ) != -1 ) {
	    vars = it.getSubTerm ().varsBoundHere ( i );
	    for ( i = 0; i < vars.size (); i++ ) 
		result = result.add ( vars.getQuantifiableVariable ( i ) );
	}
    
	return result;
    }
}
