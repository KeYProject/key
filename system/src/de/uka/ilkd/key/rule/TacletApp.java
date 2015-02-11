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

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableMapEntry;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.logic.ClashFreeSubst;
import de.uka.ilkd.key.logic.ClashFreeSubst.VariableCollectVisitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PIOPathIterator;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.RenameTable;
import de.uka.ilkd.key.logic.Semisequent;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.FormulaSV;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SkolemTermSV;
import de.uka.ilkd.key.logic.op.TermSV;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.rule.inst.GenericSortCondition;
import de.uka.ilkd.key.rule.inst.GenericSortException;
import de.uka.ilkd.key.rule.inst.IllegalInstantiationException;
import de.uka.ilkd.key.rule.inst.InstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.inst.SVInstantiations.UpdateLabelPair;
import de.uka.ilkd.key.util.Debug;

/**
 * A TacletApp object contains information required for a concrete application.
 * These information may consist of
 * <ul>
 * <li>instantiations of the schemavariables</li>
 * <li>position of the find term</li>
 * </ul>
 * Its methods <code>complete</code> or <code>sufficientlyComplete</code> are
 * used to determine if the information is complete or at least sufficient (can
 * be completed using meta variables) complete, so that is can be applied.
 */
public abstract class TacletApp implements RuleApp {
    /** the taclet for which the application information is collected */
    private final Taclet taclet;

    /**
     * contains the instantiations of the schema variables of the Taclet
     */
    protected final SVInstantiations instantiations;

    /**
     * chosen instantiations for the if sequent formulas
     */
    protected final ImmutableList<IfFormulaInstantiation> ifInstantiations;

    /**
     * set of schema variables that appear in the Taclet and need to be
     * instantiated but are not instantiated yet. This means SchemaVariables in
     * addrule-sections have to be ignored
     */
    private ImmutableSet<SchemaVariable> missingVars = null;

    /**
     * the instantiations of the following SVs must not be changed; they must
     * not be instantiated with meta variables either
     */
    protected ImmutableSet<SchemaVariable> fixedVars = DefaultImmutableSet.<SchemaVariable>nil();

    /**
     * the update context given by the current instantiations must not be
     * changed
     */
    protected boolean updateContextFixed = false;

    /**
     * constructs a TacletApp for the given taclet, with an empty instantiation
     * map
     */
    TacletApp(Taclet taclet) {
	this(taclet, SVInstantiations.EMPTY_SVINSTANTIATIONS,
		null);
    }

    TacletApp(Taclet taclet, 
	      SVInstantiations instantiations,
	      ImmutableList<IfFormulaInstantiation> ifInstantiations) {
	this.taclet = taclet;
	this.instantiations = instantiations;
	this.ifInstantiations = ifInstantiations;
    }

    /**
     * constructs a TacletApp for the given taclet. With some information about
     * required instantiations.
     */
    TacletApp(Taclet taclet, SVInstantiations instantiations) {
	this(taclet, instantiations, null);
    }

    /**
     * collects all bound variables above the occurrence of the schemavariable
     * whose prefix is given
     * 
     * @param prefix
     *            the TacletPrefix of the schemavariable
     * @param instantiations
     *            the SVInstantiations so that the find(if)-expression matches
     * @return set of the bound variables
     */
    protected static ImmutableSet<QuantifiableVariable> boundAtOccurrenceSet(
	    TacletPrefix prefix, SVInstantiations instantiations) {
	return collectPrefixInstantiations(prefix, instantiations);
    }

    /**
     * collects all bound variables above the occurrence of the schemavariable
     * whose prefix is given
     * 
     * @param prefix
     *            the TacletPrefix of the schemavariable
     * @param instantiations
     *            the SVInstantiations so that the find(if)-expression matches
     * @param pos
     *            the posInOccurrence describing the position of the
     *            schemavariable
     * @return set of the bound variables
     */
    protected static ImmutableSet<QuantifiableVariable> boundAtOccurrenceSet(
	    TacletPrefix prefix, 
	    SVInstantiations instantiations,
	    PosInOccurrence pos) {

	ImmutableSet<QuantifiableVariable> result = boundAtOccurrenceSet(prefix,
		instantiations);

	if (prefix.context())
	    result = result.union(collectBoundVarsAbove(pos));

	return result;
    }

    /**
     * collects all those logic variable that are instances of the variableSV of
     * the given prefix
     * 
     * @param pre
     *            the TacletPrefix of a SchemaVariable that is bound
     * @param instantiations
     *            the SVInstantiations to look at
     * @return the set of the logic variables whose elements are the
     *         instantiations of a bound SchemaVariable appearing in the
     *         TacletPrefix
     */
    private static ImmutableSet<QuantifiableVariable> collectPrefixInstantiations(
	    TacletPrefix pre, 
	    SVInstantiations instantiations) {

	ImmutableSet<QuantifiableVariable> instanceSet = DefaultImmutableSet.<QuantifiableVariable>nil();

	for (final SchemaVariable var : pre.prefix()) {
	    instanceSet = instanceSet
		    .add((LogicVariable) ((Term) instantiations
			    .getInstantiation(var)).op());
	}
	return instanceSet;
    }

    /**
     * returns the taclet the application information is collected for
     * 
     * @return the Taclet the application information is collected for
     */
    public Taclet taclet() {
	return taclet;
    }

    /**
     * returns the rule the application information is collected for
     * 
     * @return the Rule the application information is collected for
     */
    public Rule rule() {
	return taclet;
    }

    /**
     * returns the instantiations for the application of the Taclet at the
     * specified position.
     * 
     * @return the SVInstantiations needed to instantiate the Taclet
     */
    public SVInstantiations instantiations() {
	return instantiations;
    }

    public MatchConditions matchConditions() {
	return new MatchConditions(instantiations(), RenameTable.EMPTY_TABLE);
    }

    public ImmutableList<IfFormulaInstantiation> ifFormulaInstantiations() {
	return ifInstantiations;
    }

    /**
     * resolves collisions between bound SchemaVariables in an SVInstantiation
     * 
     * @param insts
     *            the original SVInstantiations
     * @return the resolved SVInstantiations
     */
    protected static SVInstantiations resolveCollisionVarSV(
	    					Taclet taclet,
	    					SVInstantiations insts,
	    					Services services) {

	HashMap<LogicVariable, SchemaVariable> collMap = new LinkedHashMap<LogicVariable, SchemaVariable>();

	final Iterator<ImmutableMapEntry<SchemaVariable,InstantiationEntry<?>>> it = insts
		.pairIterator();
	while (it.hasNext()) {
	    ImmutableMapEntry<SchemaVariable,InstantiationEntry<?>> pair = it.next();
	    if (pair.key() instanceof VariableSV) {
		SchemaVariable varSV = pair.key();
		Term value = (Term) pair.value().getInstantiation();
		if (!collMap.containsKey(value.op())) {
		    collMap.put((LogicVariable) value.op(), varSV);
		} else {
		    insts = replaceInstantiation(taclet, 
			    			 insts, 
			    			 varSV, 
			    			 services);
		}
	    }
	}
	return insts;
    }

    /**
     * delivers the term below the (unique) quantifier of a bound SchemaVariable
     * in the given term.
     * 
     * @param varSV
     *            the searched Bound Schemavariable
     * @param term
     *            the term to be searched in
     * @return the term below the given quantifier in the given term
     */
    private static Term getTermBelowQuantifier(SchemaVariable varSV, Term term) {
	for (int i = 0; i < term.arity(); i++) {
	    for (int j = 0; j < term.varsBoundHere(i).size(); j++) {
		if (term.varsBoundHere(i).get(j) == varSV) {
		    return term.sub(i);
		}
	    }
	    Term rec = getTermBelowQuantifier(varSV, term.sub(i));
	    if (rec != null) {
		return rec;
	    }
	}
	return null;
    }

    /**
     * delivers the term below the (unique) quantifier of a bound SchemaVariable
     * varSV in the find and if-parts of the Taclet
     * 
     * @param varSV
     *            the searched bound SchemaVariable
     * @return the term below the given quantifier in the find and if-parts of
     *         the Taclet
     */
    private static Term getTermBelowQuantifier(Taclet taclet,
	    				       SchemaVariable varSV) {
	Iterator<SequentFormula> it = taclet.ifSequent().iterator();
	while (it.hasNext()) {
	    Term result = getTermBelowQuantifier(varSV, it.next().formula());
	    if (result != null) {
		return result;
	    }
	}

	if (taclet instanceof FindTaclet) {
	    return getTermBelowQuantifier(varSV, ((FindTaclet) taclet).find());
	} else
	    return null;
    }
    
    /**
     * returns true iff the instantiation of a bound SchemaVariable contains the
     * given Logicvariable
     * 
     * @param boundVars
     *            ImmutableArray<QuantifiableVariable> with the bound SchemaVariables
     * @param x
     *            the LogicVariable that is looked for
     * @param insts
     *            the SVInstantiations where to get the necessary instantiations
     *            of the bound SchemaVariables
     * @return true iff the instantiation of a Bound Schemavariable contains the
     *         given Logicvariable
     */
    private static boolean contains(ImmutableArray<QuantifiableVariable> boundVars,
	    LogicVariable x, SVInstantiations insts) {
	for (int i = 0; i < boundVars.size(); i++) {
	    Term instance = (Term) insts
		    .getInstantiation((SchemaVariable) boundVars.get(i));
	    if (instance.op() == x) {
		return true;
	    }
	}

	return false;
    }

    /**
     * returns a new SVInstantiations that modifies the given SVInstantiations
     * insts at the bound SchemaVariable varSV to a new LogicVariable.
     */
    protected static SVInstantiations replaceInstantiation(Taclet taclet,
                                                           SVInstantiations insts, 
                                                           SchemaVariable varSV,
                                                           Services services) {
	Term term = getTermBelowQuantifier(taclet, varSV);
	LogicVariable newVariable =
	        new LogicVariable(new Name(((Term) insts.getInstantiation(varSV))
	                                    .op().name().toString() + "0"),
	                          ((Term) insts.getInstantiation(varSV)).sort());
	// __CHANGE__ How to name the new variable? TODO
	Term newVariableTerm = services.getTermBuilder().var(newVariable);
	return replaceInstantiation(insts, 
				    term, 
				    varSV, 
				    newVariableTerm,
				    services);
    }

    /**
     * returns a new SVInstantiations that modifies the given SVInstantiations
     * insts at the bound SchemaVariable u to the Term (that is a LogicVariable)
     * y.
     */
    private static SVInstantiations replaceInstantiation(
	    SVInstantiations insts, 
	    Term t, 
	    SchemaVariable u, 
	    Term y,
	    Services services) {

	SVInstantiations result = insts;
	LogicVariable x = (LogicVariable) ((Term) insts.getInstantiation(u))
		.op();
	if (t.op() instanceof SchemaVariable) {
	    if (!(t.op() instanceof VariableSV)) {
		SchemaVariable sv = (SchemaVariable) t.op();
		ClashFreeSubst cfSubst = new ClashFreeSubst(x, y, services);
		result = result.replace(sv, 
					cfSubst.apply((Term) insts.getInstantiation(sv)),
					services);
	    }
	} else {
	    for (int i = 0; i < t.arity(); i++) {
		if (!contains(t.varsBoundHere(i), x, insts)) {
		    result = replaceInstantiation(result, 
			    			  t.sub(i), 
			    			  u, 
			    			  y, 
			    			  services);
		}
	    }

	}

	result = result.replace(u, y, services);
	return result;
    }

    /**
     * applies the specified rule at the specified position if all schema
     * variables have been instantiated
     * 
     * @param goal
     *            the Goal at which the Taclet is applied
     * @param services
     *            the Services encapsulating all java information
     * @return list of new created goals
     */
    public ImmutableList<Goal> execute(Goal goal, Services services) {

        
        
	if (!complete()) {
	    throw new IllegalStateException("Tried to apply rule \n" + taclet
		    + "\nthat is not complete.");
	}
	

	if (!isExecutable(services)) {
        throw new RuntimeException("taclet application with unsatisfied 'checkPrefix': " + this);
	}
    registerSkolemConstants(services);
	goal.addAppliedRuleApp(this);
	return taclet().apply(goal, services, this);
    }

    /*
     * checks if application conditions are satisfied and returns <code>true</code> if this is the case
     */
    public boolean isExecutable(TermServices services) {
        // bugfix #1336, see bugtracker
        if (taclet instanceof RewriteTaclet) {
            ImmutableList<UpdateLabelPair> oldUpdCtx = 
                    matchConditions().getInstantiations().getUpdateContext();
            MatchConditions newConditions = ((RewriteTaclet)taclet).checkPrefix(posInOccurrence(), 
                    MatchConditions.EMPTY_MATCHCONDITIONS);
            if(newConditions == null) {
                return false;
            }
            ImmutableList<UpdateLabelPair> newUpdCtx =
                    newConditions.getInstantiations().getUpdateContext();
            if(!oldUpdCtx.equals(newUpdCtx)) {
                return false;
            }
        }
        return true;
    }

    /**
     * applies the specified rule at the specified position if all schema
     * variables have been instantiated and creates a new goal if the if-sequent
     * does not match. The new goal proves that the if sequent can be derived.
     * 
     * @param goal
     *            the Goal where to apply the rule
     * @param services
     *            the Services encapsulating all java information
     * @return list of new created goals
     */
    /*
     * public ImmutableList<Goal> executeForceIf(Goal goal, Services services) { if
     * (!complete()) { throw new
     * IllegalStateException("Applied rule not complete."); }
     * goal.addAppliedRuleApp(this); return taclet().apply(goal, services, this,
     * true); }
     */

    /**
     * calculate needed SchemaVariables that have not been instantiated yet.
     * This means to ignore SchemaVariables that appear only in addrule-sections
     * of Taclets
     * 
     * @return ImmutableSet<SchemaVariable> that need to be instantiated but are not
     */
    protected ImmutableSet<SchemaVariable> calculateNonInstantiatedSV() {
	if (missingVars == null) {
	    missingVars = DefaultImmutableSet.<SchemaVariable>nil();
	    TacletSchemaVariableCollector coll = new TacletSchemaVariableCollector(
		    instantiations());
	    coll.visitWithoutAddrule(taclet());
	    Iterator<SchemaVariable> it = coll.varIterator();
	    while (it.hasNext()) {
		SchemaVariable var = it.next();
		if (!instantiations().isInstantiated(var)) {
		    missingVars = missingVars.add(var);
		}
	    }
	}
	return missingVars;
    }


    /**
     * creates a new Tacletapp where the SchemaVariable sv is instantiated with
     * the the given Term term. Sort equality is checked. If the check fails an
     * IllegalArgumentException is thrown
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param term
     *            the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    public TacletApp addCheckedInstantiation(SchemaVariable sv, 
	    				     Term term,
	    				     Services services, 
	    				     boolean interesting) {

	if (sv instanceof VariableSV && !(term.op() instanceof LogicVariable)) {
	    throw new IllegalInstantiationException("Could not add "
		    + "the instantiation of " + sv + " because " + term
		    + " is no variable.");
	}

	MatchConditions cond = matchConditions();

	if (sv.arity() == 0) {
	    cond = sv.match(term, cond, services);
	} else {
	    cond = sv.match(term.op(), cond, services);
	}

	if (cond == null) {
	    throw new IllegalInstantiationException("Instantiation " + term
		    + " is not matched by " + sv);
	}

	cond = taclet().checkVariableConditions(sv, term, cond, services);

	if (cond == null) {
	    throw new IllegalInstantiationException("Instantiation " + term
		    + " of " + sv + "does not satisfy the variable conditions");
	}

	if (interesting) {
	    cond = cond.setInstantiations(cond.getInstantiations()
		       .makeInteresting(sv, services));
	}

	return addInstantiation(cond.getInstantiations(), services);

    }

    /**
     * returns the variables that have not yet been instantiated and need to be
     * instantiated to apply the Taclet. (These are not all SchemaVariables like
     * the one that appear only in the addrule sections)
     * 
     * @return ImmutableSet<SchemaVariable> with SchemaVariables that have not been
     *         instantiated yet
     */
    public ImmutableSet<SchemaVariable> uninstantiatedVars() {
	return calculateNonInstantiatedSV();
    }

    /**
     * @return A TacletApp with this.sufficientlyComplete() or null
     */
    public final TacletApp tryToInstantiate(Services services) {
	final VariableNamer varNamer = services.getVariableNamer();
	final TermBuilder tb = services.getTermBuilder();

	TacletApp app = this;
	ImmutableList<String> proposals = ImmutableSLList.<String>nil();

	for (final SchemaVariable sv : uninstantiatedVars()) {
	    if (sv.arity() != 0) {
		continue;
	    }

	    if (sv.sort() == ProgramSVSort.VARIABLE) {
		String proposal = varNamer
			.getSuggestiveNameProposalForProgramVariable(sv, this,
				services, proposals);
		ProgramElement pe = app.getProgramElement(proposal, sv, services);
		app = app.addCheckedInstantiation(sv, pe, services, true);
		proposals = proposals.append(proposal);
	    } else if (sv.sort() == ProgramSVSort.LABEL) {
		boolean nameclash;
		do {
		    String proposal = VariableNameProposer.DEFAULT.getProposal(
			    this, sv, services, null, proposals);
		    ProgramElement pe = app.getProgramElement(proposal, sv, services);
		    proposals = proposals.prepend(proposal);
		    try {
			app = app.addCheckedInstantiation(sv, pe, services,
				true);
		    } catch (IllegalInstantiationException iie) {
			// name clash
			nameclash = true;
		    }
                    // FIXME: This loop is never executed more than once
                    // The following line might belong to the try-block.
                    // Leave it untouched, however, since no problems
                    // reported with this established code. MU 10-2012
		    nameclash = false;
		} while (nameclash);
	    } else if (sv instanceof SkolemTermSV) {
		// if the sort of the schema variable is generic,
		// ensure that it is instantiated
		app = forceGenericSortInstantiation(app, sv, services);
		if (app == null)
		    return null;

		String proposal = VariableNameProposer.DEFAULT.getProposal(app,
			sv, services, null, proposals);

		proposals = proposals.append(proposal);

		app = app.createSkolemConstant(proposal, sv, true, services);

	    } else if (sv instanceof VariableSV) {
		// if the sort of the schema variable is generic,
		// ensure that it is instantiated
		app = forceGenericSortInstantiation(app, sv, services);
		if (app == null)
		    return null;

		String proposal;
		Collection<String> conflictNames = collectClashNames(sv, services);
		do {
		    proposal = VariableNameProposer.DEFAULT.getProposal(
		            this, sv, services, null, proposals);
		    proposals = proposals.prepend(proposal);
		} while(conflictNames.contains(proposal));

		LogicVariable v = new LogicVariable(new Name(proposal), getRealSort(sv, services));

		app = app
			.addCheckedInstantiation(sv, tb.var(v), services, true);
	    } else {
		return null;
	    }
	}

	if (app != this) {
	    final MatchConditions appMC = app.taclet().checkConditions(
		    app.matchConditions(), services);
	    if (appMC == null) {
		return null;
	    } else {
		app = app.setMatchConditions(appMC, services);
	    }
	}

	if (!app.complete()) {
	    return null;
	}
	return app;
    }

    /**
     * Collect names which would result in a clash for a new logical variable.
     * 
     * The clashing names include the names of the bound and unbound variables
     * of "notFreeIn" clauses. Additionally, equally-named program variables are
     * avoided.
     * 
     * While this analysis is not strictly necessary (two different variables
     * may bear the same name), it is vital not to cause confusion with the
     * user.
     * 
     * @param sv
     *            the schema variable to instantiate with a fresh variable, not
     *            <code>null</code>
     * @param services
     *            the services object, not <code>null</code>
     * @return a fresh created collection of strings in which a freshly created
     *         variable name should not fall.
     */
    private Collection<String> collectClashNames(SchemaVariable sv, TermServices services) {
        Collection<String> result = new LinkedHashSet<String>();
        VariableCollectVisitor vcv = new VariableCollectVisitor();
        Iterator<NotFreeIn> it = taclet().varsNotFreeIn();
        while(it.hasNext()) {
            NotFreeIn nv;
            nv = it.next();
            if(nv.first() == sv) {
                Term term = (Term) instantiations.getInstantiation(nv.second());
                if (term != null) {
                    term.execPostOrder(vcv);
                }
            }
        }

        for (QuantifiableVariable var : vcv.vars()) {
            result.add(var.name().toString());
        }

        for(Named progvar : services.getNamespaces().programVariables().allElements()) {
            result.add(progvar.name().toString());
        }

        return result;
    }

    /**
     * If the sort of the given schema variable is generic, add a condition to
     * the instantiations of the given taclet app that requires the sort to be
     * instantiated
     * 
     * @return the new taclet app, or <code>null</code> if the sort of
     *         <code>sv</code> is generic and cannot be instantiated (at least
     *         at the time)
     */
    private static TacletApp forceGenericSortInstantiation(TacletApp app,
	    						   SchemaVariable sv,
	    						   Services services) {
	final GenericSortCondition c = GenericSortCondition.forceInstantiation(
		sv.sort(), false);
	if (c != null) {
	    try {
		app = app.setInstantiation(app.instantiations().add(c, services), 
			                   services);
	    } catch (GenericSortException e) {
		return null;
	    }
	}
	return app;
    }

    /**
     * Examine all schema variables of the taclet that are currently not
     * instantiated, and for each one whose sort is generic add a condition to
     * the instantiations object <code>insts</code> that requires this sort to
     * be instantiated
     * 
     * @return the instantiations object after adding all the conditions, or
     *         <code>null</code> if any of the generic sorts found cannot be
     *         instantiated (at least at the time)
     */
    private SVInstantiations forceGenericSortInstantiations(SVInstantiations insts,
                                                            Services services) {
	// force all generic sorts to be instantiated
	try {
	    for (final SchemaVariable sv : uninstantiatedVars()) {
		final GenericSortCondition c = GenericSortCondition
			.forceInstantiation(sv.sort(), true);
		if (c != null)
		    insts = insts.add(c, services);
	    }
	} catch (GenericSortException e) {
	    Debug.fail("TacletApp cannot be made complete");
	}
	return insts;
    }

    /**
     * @param services
     *            the Services class allowing access to the type model
     * @return p_s iff p_s is not a generic sort, the concrete sort p_s is
     *         instantiated with currently otherwise
     * @throws GenericSortException
     *             iff p_s is a generic sort which is not yet instantiated
     */
    public Sort getRealSort(SchemaVariable p_sv, TermServices services) {
	return instantiations().getGenericSortInstantiations().getRealSort(
		p_sv, services);
    }

    /**
     * Create a new constant named "instantiation" and instantiate "sv" with.
     * This constant will later (by "createSkolemFunctions") be replaced by a
     * function having the occurring metavariables as arguments
     * 
     * @param services
     *            the Services class allowing access to the type model
     */
    public TacletApp createSkolemConstant(String instantiation,
	    		                  SchemaVariable sv, 
	    		                  boolean interesting, 
	    		                  Services services) {
	return createSkolemConstant(instantiation, 
				    sv,
				    getRealSort(sv, services), 
				    interesting,
				    services);
    }

    public TacletApp createSkolemConstant(String instantiation,
	    				  SchemaVariable sv, 
	    				  Sort sort, 
	    				  boolean interesting,
	    				  Services services) {
	final Function c 
		= new Function(new Name(instantiation), sort, true, new Sort[0]);
	return addInstantiation(sv, services.getTermBuilder().func(c), interesting, services);
    }
    
    
    public void registerSkolemConstants(TermServices services) {
	final SVInstantiations insts = instantiations();
	final Iterator<SchemaVariable> svIt = insts.svIterator();
	while(svIt.hasNext()) {
	    final SchemaVariable sv = svIt.next();
	    if(sv instanceof SkolemTermSV) {
		final Term inst = (Term) insts.getInstantiation(sv);
		final Namespace functions =
                        services.getNamespaces().functions();

                // skolem constant might already be registered in
                // case it is used in the \addrules() section of a rule
                if (functions.lookup(inst.op().name()) == null) {
                    functions.addSafely(inst.op());
                }
	    }
	}
    }    
    
    
    /**
     * adds a new instantiation to this TacletApp
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param term
     *            the Term the SchemaVariable is instantiated with
     * @return the new TacletApp
     */
    public abstract TacletApp addInstantiation(SchemaVariable sv, 
	    				       Term term,
	    				       boolean interesting,
	    				       Services services);

    public abstract TacletApp addInstantiation(SchemaVariable sv,
	    				       Object[] list, 
	    				       boolean interesting,
	    				       Services services);

    /**
     * adds a new instantiation to this TacletApp. This method does not check
     * (beside some very rudimentary tests) if the instantiation is possible. If
     * you cannot guarantee that adding the entry <code>(sv, pe)</code> will
     * result in a valid taclet instantiation, you have to use
     * {@link #addCheckedInstantiation(SchemaVariable, ProgramElement, Services, boolean)}
     * instead
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param pe
     *            the ProgramElement the SV is instantiated with
     * @param interesting
     *            a boolean marking if the instantiation of this sv needs to be
     *            saved for later proof loading (<code>interesting==true</code>)
     *            or if it can be derived deterministically (e.g. by matching) (
     *            <code>interesting==false</code>)
     * @return a new taclet application equal to this one but including the
     *         newly added instantiation entry <code>(sv, pe)</code>
     */
    public abstract TacletApp addInstantiation(SchemaVariable sv,
	    				       ProgramElement pe, 
	    				       boolean interesting,
	    				       Services services);

    /**
     * checks if the instantiation of <code>sv</code> with <code>pe</code> is
     * possible. If the resulting instantiation is valid a new taclet
     * application with an extended instantiation mapping is created and
     * returned. Otherwise an exception is thrown.
     * 
     * @param sv
     *            the SchemaVariable to be instantiated
     * @param pe
     *            the ProgramElement the SV is instantiated with
     * @param services
     *            the Services
     * @param interesting
     *            a boolean marking if the instantiation of this sv needs to be
     *            saved for later proof loading (<code>interesting==true</code>)
     *            or if it can be derived deterministically (e.g. by matching) (
     *            <code>interesting==false</code>)
     * @return a new taclet application equal to this one but including the
     *         newly added instantiation entry <code>(sv, pe)</code>, if the
     *         instantiation results in a valid taclet application otherwise an
     *         exception is thrown
     * @throws IllegalInstantiationException
     *             exception thrown if <code>sv</code> cannot be instantiated
     *             with <code>pe</code> no matter if in general or due to side
     *             conditions posed by this particular application
     * 
     */
    public TacletApp addCheckedInstantiation(SchemaVariable sv,
	    				     ProgramElement pe, 
	    				     Services services, 
	    				     boolean interesting) {

	MatchConditions cond = matchConditions();

	if (sv instanceof ProgramSV) {
            cond = sv.match(pe, cond, services);
	} else {
	    throw new IllegalInstantiationException(
		    "Cannot match program element '" + pe + "'("
			    + (pe == null ? null : pe.getClass().getName())
			    + ") to non program sv " + sv);
	}

	if (cond == null) {
	    throw new IllegalInstantiationException("Instantiation " + pe + "("
		    + (pe == null ? null : pe.getClass().getName())
		    + ") is not matched by " + sv);
	}

	cond = taclet().checkConditions(cond, services);

	if (cond == null) {
	    throw new IllegalInstantiationException("Instantiation " + pe
		    + " of " + sv + "does not satisfy variable conditions");
	}

	if (interesting) {
	    cond = cond.setInstantiations(cond.getInstantiations()
		    .makeInteresting(sv, services));
	}

	return addInstantiation(cond.getInstantiations(), services);

    }

    public TacletApp addInstantiation(SchemaVariable sv, 
	    			      Name name, 
	    			      Services services) {
	return addInstantiation(SVInstantiations.EMPTY_SVINSTANTIATIONS
				.addInteresting(sv, name, services), 
				services);
    }

    /**
     * creates a new Taclet application containing all the instantiations given
     * by the SVInstantiations
     * 
     * @param svi
     *            the SVInstantiations whose entries are the needed
     *            instantiations
     * @return the new Taclet application
     */
    public abstract TacletApp addInstantiation(SVInstantiations svi,
	    				       Services services);

    /**
     * creates a new Taclet application containing all the instantiations given
     * by the SVInstantiations and forget the old ones
     * 
     * @param svi
     *            the SVInstantiations whose entries are the needed
     *            instantiations
     * @return the new Taclet application
     */
    protected abstract TacletApp setInstantiation(SVInstantiations svi,
	    				          Services services);

    /**
     * creates a new Taclet application containing all the instantiations,
     * constraints and new metavariables given by the mc object and forget the
     * old ones
     */
    public abstract TacletApp setMatchConditions(MatchConditions mc,
	    					 Services services);

    /**
     * creates a new Taclet application containing all the instantiations,
     * constraints, new metavariables and if formula instantiations given and
     * forget the old ones
     */
    protected abstract TacletApp setAllInstantiations(
	    	MatchConditions mc,
	    	ImmutableList<IfFormulaInstantiation> ifInstantiations,
	    	Services services);

    /**
     * Creates a new Taclet application by matching the given formulas against
     * the formulas of the if sequent, adding SV instantiations, constraints and
     * metavariables as needed. This will fail if the if formulas have already
     * been instantiated.
     */
    public TacletApp setIfFormulaInstantiations(
	    ImmutableList<IfFormulaInstantiation> p_list, 
	    Services p_services) {
	assert p_list != null && ifInstsCorrectSize(taclet, p_list)
		&& ifInstantiations == null : "If instantiations list has wrong size or is null "
		+ "or the if formulas have already been instantiated";

	MatchConditions mc = taclet().matchIf(p_list.iterator(),
		matchConditions(), p_services);

	return mc == null ? null : setAllInstantiations(mc, p_list, p_services);
    }

    /**
     * Find all possible instantiations of the if sequent formulas within the
     * sequent "p_seq".
     * 
     * @return a list of tacletapps with the found if formula instantiations
     */
    public ImmutableList<TacletApp> findIfFormulaInstantiations(
	    Sequent p_seq,
	    Services p_services) {

	Debug.assertTrue(ifInstantiations == null,
		"The if formulas have already been instantiated");

	if (taclet().ifSequent().isEmpty())
	    return ImmutableSLList.<TacletApp>nil().prepend(this);

	return findIfFormulaInstantiationsHelp(
		createSemisequentList(taclet().ifSequent() // Matching starting
			.succedent()), // with the last formula
		createSemisequentList(taclet().ifSequent().antecedent()),
		IfFormulaInstSeq.createList(p_seq, false), IfFormulaInstSeq
			.createList(p_seq, true),
		ImmutableSLList.<IfFormulaInstantiation>nil(), matchConditions(),
		p_services);

    }

    /**
     * Recursive function for matching the remaining tail of an if sequent
     * 
     * @param p_ifSeqTail
     *            tail of the current semisequent as list
     * @param p_ifSeqTail2nd
     *            the following semisequent (i.e. antecedent) or null
     * @param p_toMatch
     *            list of the formulas to match the current if semisequent
     *            formulas with
     * @param p_toMatch2nd
     *            list of the formulas of the antecedent
     * @param p_matchCond
     *            match conditions until now, i.e. after matching the first
     *            formulas of the if sequent
     */
    private ImmutableList<TacletApp> findIfFormulaInstantiationsHelp(
	    ImmutableList<SequentFormula> p_ifSeqTail,
	    ImmutableList<SequentFormula> p_ifSeqTail2nd,
	    ImmutableList<IfFormulaInstantiation> p_toMatch,
	    ImmutableList<IfFormulaInstantiation> p_toMatch2nd,
	    ImmutableList<IfFormulaInstantiation> p_alreadyMatched,
	    MatchConditions p_matchCond, Services p_services) {

	while (p_ifSeqTail.isEmpty()) {
	    if (p_ifSeqTail2nd == null) {
		// All formulas have been matched, collect the results
		TacletApp res = setAllInstantiations(p_matchCond,
					             p_alreadyMatched,
					             p_services);
		if (res != null)
		    return ImmutableSLList.<TacletApp>nil().prepend(res);
		return ImmutableSLList.<TacletApp>nil();
	    } else {
		// Change from succedent to antecedent
		p_ifSeqTail = p_ifSeqTail2nd;
		p_ifSeqTail2nd = null;
		p_toMatch = p_toMatch2nd;
	    }
	}

	// Match the current formula
	IfMatchResult mr = taclet().matchIf(p_toMatch.iterator(),
		p_ifSeqTail.head().formula(), p_matchCond, p_services);

	// For each matching formula call the method again to match
	// the remaining terms
	ImmutableList<TacletApp> res = ImmutableSLList.<TacletApp>nil();
	Iterator<IfFormulaInstantiation> itCand = mr.getFormulas().iterator();
	Iterator<MatchConditions> itMC = mr.getMatchConditions().iterator();
	p_ifSeqTail = p_ifSeqTail.tail();
	while (itCand.hasNext()) {
	    res = res.prepend(findIfFormulaInstantiationsHelp(p_ifSeqTail,
		    p_ifSeqTail2nd, p_toMatch, p_toMatch2nd, p_alreadyMatched
			    .prepend(itCand.next()), itMC.next(), p_services));
	}

	return res;
    }

    private ImmutableList<SequentFormula> createSemisequentList(Semisequent p_ss) {
	ImmutableList<SequentFormula> res = ImmutableSLList.<SequentFormula>nil();

        for (Object p_s : p_ss) res = res.prepend((SequentFormula) p_s);

	return res;
    }

    /**
     * returns a new PosTacletApp that is equal to this TacletApp except that
     * the position is set to the given PosInOccurrence.
     * 
     * <p><b>CAUTION:</b> If you call this method, consider to call 
     * {@link NoPosTacletApp#matchFind(PosInOccurrence, Services)} first (if
     * applicable) as otherwise the TacletApp may become invalid. 
     * (This happened sometimes during interactive proofs).
     * 
     * @param pos
     *            the PosInOccurrence of the newl created PosTacletApp
     * @return the new TacletApp
     */
    public PosTacletApp setPosInOccurrence(PosInOccurrence pos, 
	    			           Services services) {
	if (taclet() instanceof NoFindTaclet) {
	    throw new IllegalStateException("Cannot add position to an taclet"
		    + " without find");
	}
	return PosTacletApp.createPosTacletApp(
		(FindTaclet) taclet(),
		instantiations(), 
		ifFormulaInstantiations(), 
		pos,
		services);
    }

    /**
     * returns true iff all necessary informations are collected, so that the
     * Taclet can be applied.
     * 
     * @return true iff all necessary informations are collected, so that the
     *         Taclet can be applied.
     */
    public abstract boolean complete();

  
    /**
     * @return true iff the if instantiation list is not null or no if sequent
     *         is needed
     */
    public boolean ifInstsComplete() {
	return ifInstantiations != null || (taclet().ifSequent().isEmpty());
    }

    /**
     * returns the PositionInOccurrence (representing a SequentFormula and a
     * position in the corresponding formula)
     * 
     * @return the PosInOccurrence
     */
    public abstract PosInOccurrence posInOccurrence();

    /**
     * compares the given Object with this one and returns true iff both are
     * from type TacletApp with equal taclets, instantiations and positions.
     */
    public boolean equals(Object o) {
       if (o == this)
          return true;
       if (o == null || o.getClass()  != this.getClass()) {
          return false;
       }
       final TacletApp s = (TacletApp) o;
       return (s.taclet.equals(taclet) && s.instantiations.equals(
             instantiations));// && (ifInstantiations == null ? s.ifInstantiations == null : 
                //ifInstantiations.equals(s.ifInstantiations));
    }

    public int hashCode() {
       int result = 17;
       result = 37 * result + taclet.hashCode();
       result = 37 * result + instantiations.hashCode();
       result = 37 * result + (ifInstantiations == null ? 0 : ifInstantiations.hashCode()); 
       return result;
    }

    public String toString() {
	return "Application of Taclet " + taclet() + " with "
		+ instantiations() + " and " + ifFormulaInstantiations();
    }

    /**
     * checks if there are name conflicts (i.e. there are two matched bound
     * SchemaVariable that are matched to variables with an equal name); if yes
     * a new TacletApp is returned that equals this TacletApp except that the
     * name conflict is resolved by replacing the instantiation of one of the
     * conflict-causing SchemaVariables by a bound SchemaVariable with a new
     * name; if the check is negative, the same TacletApp is returned.
     * 
     * @return a conflict resolved TacletApp, remainder equal to this TacletApp
     */
    public TacletApp prepareUserInstantiation(Services services) {
	TacletApp result = this;
	SchemaVariable varSV = varSVNameConflict();
	while (varSV != null) {
	    result = setInstantiation(replaceInstantiation(
            		    			taclet, 
            		    			result.instantiations(), 
            		    			varSV,
            		    			services),
            		    	      services);
	    varSV = result.varSVNameConflict();
	}
	return result;
    }

    protected abstract ImmutableSet<QuantifiableVariable> contextVars(SchemaVariable sv);

    /**
     * creates a new variable namespace by adding names of the instantiations of
     * the schema variables in the context of the given schema variable and (if
     * the TacletApp's prefix has the context flag set) by adding names of the
     * logic variables of the context.
     * 
     * @param sv
     *            the schema variable to be considered
     * @param var_ns
     *            the old variable namespace
     * @return the new created variable namespace
     */
    public Namespace extendVarNamespaceForSV(Namespace var_ns, SchemaVariable sv) {
	Namespace ns = new Namespace(var_ns);
	Iterator<SchemaVariable> it = taclet().getPrefix(sv).prefix()
		.iterator();
	while (it.hasNext()) {
	    LogicVariable var = (LogicVariable) ((Term) instantiations()
		    .getInstantiation(it.next())).op();
	    ns.add(var);
	}
	if (taclet().getPrefix(sv).context()) {
	    Iterator<QuantifiableVariable> lit = contextVars(sv).iterator();
	    while (lit.hasNext()) {
		ns.add(lit.next());
	    }
	}
	return ns;
    }

    /**
     * create a new function namespace by adding all newly instantiated skolem
     * symbols to a new namespace.
     * 
     * @author mulbrich
     * @param func_ns
     *            the original function namespace
     * @return the new function namespace that bases on the original one
     */
    public Namespace extendedFunctionNameSpace(Namespace func_ns) {
	Namespace ns = new Namespace(func_ns);
	Iterator<SchemaVariable> it = instantiations.svIterator();
	while (it.hasNext()) {
	    SchemaVariable sv = it.next();
	    if (sv instanceof SkolemTermSV) {
		Term inst = (Term) instantiations.getInstantiation(sv);
		ns.addSafely(inst.op());
	    }
	}
	return ns;
    }

    /**
     * returns the bound SchemaVariable that causes a name conflict (i.e. there
     * are two matched bound SchemaVariables that are matched to variables with
     * an equal name, the returned SchemaVariable is (an arbitrary) one of these
     * SchemaVariables) or null if there is no such conflict
     * 
     * @return null iff there is no conflict and one of the conflict-causing
     *         bound SchemaVariables
     */
    public SchemaVariable varSVNameConflict() {
        for (SchemaVariable schemaVariable : uninstantiatedVars()) {
            SchemaVariable sv = schemaVariable;
	    if (sv instanceof TermSV || sv instanceof FormulaSV) {
		TacletPrefix prefix = taclet().getPrefix(sv);
		HashSet<Name> names = new LinkedHashSet<Name>();
                if (prefix.context()) {
                    for (QuantifiableVariable quantifiableVariable : contextVars(sv)) {
                        names.add(quantifiableVariable.name());
                    }
                }
                Iterator<SchemaVariable> varSVIt = prefix.iterator();
                while (varSVIt.hasNext()) {
                    SchemaVariable varSV = varSVIt.next();
                    Term inst = (Term)
                            instantiations().getInstantiation(varSV);
                    if (inst != null) {
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
     * @return true iff the list of if instantiations has the correct size or is
     *         null
     */
    protected static boolean ifInstsCorrectSize(Taclet p_taclet,
	    ImmutableList<IfFormulaInstantiation> p_list) {
	return p_list == null
		|| p_list.size() == (p_taclet.ifSequent().antecedent().size() + p_taclet
			.ifSequent().succedent().size());
    }

    /**
     * @return true iff the Taclet may be applied for the given mode
     *         (interactive/non-interactive, activated rule sets)
     */
    public boolean admissible(boolean interactive, ImmutableList<RuleSet> ruleSets) {
	return taclet().admissible(interactive, ruleSets);
    }

    public ProgramElement getProgramElement(String instantiation,
                                            SchemaVariable sv,
                                            Services services) {
        Sort svSort = sv.sort();
        if (svSort == ProgramSVSort.LABEL) {
            return VariableNamer.parseName(instantiation);
        } else if (svSort == ProgramSVSort.VARIABLE ) {
            NewVarcond nvc = taclet.varDeclaredNew(sv);
            if (nvc != null) {
        	KeYJavaType kjt;
        	Object o = nvc.getTypeDefiningObject();
        	JavaInfo javaInfo = services.getJavaInfo ();
        	if (o instanceof SchemaVariable) {
                    final TypeConverter tc = services.getTypeConverter();
        	    final SchemaVariable peerSV = (SchemaVariable)o;
        	    final Object peerInst = instantiations().getInstantiation(peerSV);
                    if(peerInst instanceof TypeReference){
                        kjt = ((TypeReference) peerInst).getKeYJavaType();
                    } else {
                        Expression peerInstExpr;
                        if(peerInst instanceof Term) {
                            peerInstExpr = tc.convertToProgramElement((Term)peerInst);
                        } else {
                            peerInstExpr = (Expression)peerInst;
                        }
                        kjt = tc.getKeYJavaType(peerInstExpr, 
                        			instantiations().getContextInstantiation().activeStatementContext());
                    }
        	} else {
        	    kjt = javaInfo.getKeYJavaType((Type)o);
        	}
                assert kjt != null : "could not find kjt for: " + o;
        	return new LocationVariable
        	    (VariableNamer.parseName(instantiation), kjt);
            }
        }
        return null;
    }

    /**
     * checks if the variable conditions of type 'x not free in y' are hold by
     * the found instantiations. The variable conditions is used implicit in the
     * prefix. (Used to calculate the prefix)
     * 
     * @param taclet
     *            the Taclet that is tried to be instantiated. A match for the
     *            find (or/and if) has been found.
     * @param instantiations
     *            the SVInstantiations so that the find(if) expression matches
     * @param pos
     *            the PosInOccurrence where the Taclet is applied
     * @return true iff all variable conditions x not free in y are hold
     */
    public static boolean checkVarCondNotFreeIn(Taclet taclet,
	    SVInstantiations instantiations, PosInOccurrence pos) {

	Iterator<SchemaVariable> it = instantiations.svIterator();
	while (it.hasNext()) {
	    SchemaVariable sv = it.next();
	    if (sv instanceof TermSV || sv instanceof FormulaSV) {
		if (!((Term) instantiations.getInstantiation(sv)).freeVars()
			.subset(
				boundAtOccurrenceSet(taclet.getPrefix(sv),
					instantiations, pos))) {

		    return false;
		}
	    }
	}
	return true;
    }

    /**
     * collects all bound vars that are bound above the subterm described by the
     * given term position information
     * 
     * @param pos
     *            the PosInOccurrence describing a subterm in Term
     * @return a set of logic variables that are bound above the specified
     *         subterm
     */
    protected static ImmutableSet<QuantifiableVariable> collectBoundVarsAbove(
	    PosInOccurrence pos) {
	ImmutableSet<QuantifiableVariable> result = DefaultImmutableSet.<QuantifiableVariable>nil();

	PIOPathIterator it = pos.iterator();
	int i;
	ImmutableArray<QuantifiableVariable> vars;

	while ((i = it.next()) != -1) {
	    vars = it.getSubTerm().varsBoundHere(i);
	    for (i = 0; i < vars.size(); i++)
		result = result.add(vars.get(i));
	}

	return result;
    }
}
