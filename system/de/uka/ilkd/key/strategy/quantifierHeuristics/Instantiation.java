// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                Universitaet Koblenz-Landau, Germany
//                Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.IteratorOfConstrainedFormula;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SetAsListOfTerm;
import de.uka.ilkd.key.logic.SetOfTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.CastFunctionSymbol;
import de.uka.ilkd.key.logic.op.IteratorOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.MapAsListFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.MapFromQuantifiableVariableToTerm;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.strategy.LongRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

class Instantiation {

	private final static TermBuilder tb = TermBuilder.DF;

	/**universally quatifiable variable bound in<code>allTerm</code> */
	private final QuantifiableVariable firstVar;

    private final Term matrix;
    
	/** Literals occurring in the sequent at hand. This is used for branch
     * prediction */
	private SetOfTerm assumedLiterals = SetAsListOfTerm.EMPTY_SET;

	/** HashMap from instance(<code>Term</code>) to cost <code>Long</code> */
	private final Map instancesWithCosts = new HashMap ();

	/**the <code>TriggersSet</code> of this <code>allTerm</code>*/
	private final TriggersSet triggersSet;
	
	/**Terms bound in every formula on <code>goal</code>*/
	private final SetOfTerm matchedTerms;

	private Instantiation(Term allterm, Sequent seq) {
        firstVar = allterm.varsBoundHere ( 0 ).getQuantifiableVariable ( 0 );
        matrix = TriggerUtils.discardQuantifiers ( allterm );
        matchedTerms = sequentToTerms ( seq );
        triggersSet = TriggersSet.create ( allterm );
        assumedLiterals = initAssertLiterals ( seq );
        addInstances ( matchedTerms );
    }

    
    private static Term lastQuantifiedFormula = null;
    private static Sequent lastSequent = null;
    private static Instantiation lastResult = null;
    
	static Instantiation create(Term qf, Sequent seq) {
        if ( qf == lastQuantifiedFormula && seq == lastSequent )
            return lastResult;
        
        lastQuantifiedFormula = qf;
        lastSequent = seq;
        lastResult = new Instantiation ( qf, seq );
        
        return lastResult;
    }

	private static SetOfTerm sequentToTerms(Sequent seq) {
        SetOfTerm res = SetAsListOfTerm.EMPTY_SET;
        IteratorOfConstrainedFormula it = seq.iterator ();
        while ( it.hasNext () )
            res = res.add ( it.next ().formula () );
        return res;
    }

	
	/**
	 * @param terms
	 *            on which trigger are doning matching search every
	 *            <code>Substitution</code> s by matching
	 *            <code>triggers</code> from <code>triggersSet</code> to
	 *            <code>terms</code> compute their cost and store the pair of
	 *            instance (Term) and cost(Long) in
	 *            <code>instancesCostCache</code>
	 */
	private void addInstances(SetOfTerm terms) {
        final IteratorOfTrigger trs = triggersSet.getAllTriggers ().iterator ();
        while ( trs.hasNext () ) {
            final SetOfSubstitution subs =
                trs.next ().getSubstitutionsFromTerms ( terms );
            final IteratorOfSubstitution it = subs.iterator ();
            while ( it.hasNext () )
                addInstance ( it.next () );
        }
        
//        if ( instancesWithCosts.isEmpty () )
            // ensure that there is always at least one instantiation
//            addArbitraryInstance ();
    }

    private void addArbitraryInstance() {
        MapFromQuantifiableVariableToTerm varMap =
            MapAsListFromQuantifiableVariableToTerm.EMPTY_MAP;
        
        final IteratorOfQuantifiableVariable it =
            triggersSet.getUniQuantifiedVariables().iterator();
        while ( it.hasNext () ) {
            final QuantifiableVariable v = it.next();
            final Term inst = createArbitraryInstantiation
                ( v, Main.getInstance ().mediator ().getServices () );
            varMap = varMap.put ( v, inst );
        }
        
        addInstance ( new Substitution ( varMap ) );
    }

    private Term createArbitraryInstantiation(QuantifiableVariable var,
                                              Services services) {
        return tb.func ( ( (AbstractSort)var.sort () ).getCastSymbol (),
                         tb.zTerm ( services, "0" ) );
    }

    private void addInstance(Substitution sub) {
        final long cost =
            PredictCostProver.computerInstanceCost ( sub, getMatrix(),
                                                     assumedLiterals );
        if ( cost != -1 ) addInstance ( sub, cost );
    }

    /**
     * add instance of <code>var</code> in <code>sub</code> with
     * <code>cost</code> to <code>instancesCostCache</code> if this instance
     * is exist, compare thire cost and store the less one.
     * 
     * @param sub
     * @param cost
     */
	private void addInstance(Substitution sub, long cost) {
        final Term inst = sub.getSubstitutedTerm ( firstVar );
        final Long oldCost = (Long)instancesWithCosts.get ( inst );
        if ( oldCost == null || oldCost.longValue () >= cost )
            instancesWithCosts.put ( inst, new Long ( cost ) );
    }

	/**
	 * @param seq
	 * @return all literals in antesequent, and all negation of literal in
	 *         succedent
	 */
	private SetOfTerm initAssertLiterals(Sequent seq) {
        SetOfTerm assertLits = SetAsListOfTerm.EMPTY_SET;
        final IteratorOfConstrainedFormula anteIt = seq.antecedent ().iterator ();
        while ( anteIt.hasNext () ) {
            final Term atom = anteIt.next ().formula ();
            final Operator op = atom.op ();
            if ( !( op == Op.ALL || op == Op.EX ) )
                assertLits = assertLits.add ( atom );
        }
        final IteratorOfConstrainedFormula succIt = seq.succedent ().iterator ();
        while ( succIt.hasNext () ) {
            final Term atom = succIt.next ().formula ();
            final Operator op = atom.op ();
            if ( !( op == Op.ALL || op == Op.EX ) )
                assertLits = assertLits.add ( tb.not ( atom ) );
        }
        return assertLits;
    }
    
    
    
    
	/**
	 * Try to find the cost of an instance(inst) according its quantified 
	 * formula and current goal. 
	 */
	static RuleAppCost computeCost(Term inst, Term form, Sequent seq) {
        return Instantiation.create ( form, seq ).computeCostHelp ( inst );
    }

    private RuleAppCost computeCostHelp(Term inst) {
        Long cost = (Long)instancesWithCosts.get ( inst );
        if ( cost == null && ( inst.op () instanceof CastFunctionSymbol ) )
            cost = (Long)instancesWithCosts.get ( inst.sub ( 0 ) );

        if ( cost == null ) {
//            if (triggersSet)
            return TopRuleAppCost.INSTANCE;
        }
        if ( cost.longValue () == -1 ) return TopRuleAppCost.INSTANCE;

        return LongRuleAppCost.create ( cost.longValue () );
    }

	/**get all instances from instancesCostCache subsCache*/
	SetOfTerm getSubstitution() {
        SetOfTerm res = SetAsListOfTerm.EMPTY_SET;
        final Iterator it = instancesWithCosts.keySet ().iterator ();
        while ( it.hasNext () )
            res = res.add ( (Term)it.next () );
        return res;
    }

    private Term getMatrix() {
        return matrix;
    }

}
