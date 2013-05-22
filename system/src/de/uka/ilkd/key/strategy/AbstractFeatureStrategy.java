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


package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.rulefilter.IHTacletFilter;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.feature.instantiator.BackTrackingManager;
import de.uka.ilkd.key.strategy.feature.instantiator.ForEachCP;
import de.uka.ilkd.key.strategy.feature.instantiator.OneOfCP;
import de.uka.ilkd.key.strategy.feature.instantiator.SVInstantiationCP;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.*;
import de.uka.ilkd.key.strategy.termgenerator.TermGenerator;


/**
 *
 */
public abstract class AbstractFeatureStrategy implements Strategy {

    private final Proof proof;

    protected AbstractFeatureStrategy (Proof proof) {
        this.proof = proof;
    }

    /**
     * @return Returns the proof.
     */
    protected Proof getProof () {
        return proof;
    }

    /**
     * @param heuristics
     * @param thenFeature
     * @return the conditional feature return true when the rule belongs to one of the given heuristics
     */
    protected Feature ifHeuristics (String[] heuristics, Feature thenFeature) {
        return ConditionalFeature.createConditional (
                getFilterFor ( heuristics ),
                thenFeature );
    }

    /**
     * @param heuristics
     * @param thenFeature
     * @param elseFeature
     */
    protected Feature ifHeuristics (String[] heuristics,
                                    Feature thenFeature,
                                    Feature elseFeature) {
        return ConditionalFeature.createConditional ( getFilterFor ( heuristics ),
                                                      thenFeature,
                                                      elseFeature );
    }

    protected Feature longConst (long a) {
        return ConstFeature.createConst ( c ( a ) );
    }

    protected Feature inftyConst () {
        return ConstFeature.createConst ( infty () );
    }
    
    protected TermFeature any() {
        return longTermConst ( 0 );
    }
    
    protected TermFeature longTermConst(long a) {
        return ConstTermFeature.createConst ( c ( a ) );
    }

    protected TermFeature inftyTermConst() {
        return ConstTermFeature.createConst ( infty () );
    }

    protected Feature add (Feature a, Feature b) {
        return BinarySumFeature.createSum ( a, b );
    }

    protected Feature add (Feature a, Feature b, Feature c) {
        return TernarySumFeature.createSum ( a, b, c );
    }

    protected TermFeature add (TermFeature a, TermFeature b) {
        return BinarySumTermFeature.createSum ( a, b );
    }

    protected TermFeature add (TermFeature a, TermFeature b, TermFeature c) {
        // could be done more efficiently
        return add ( a, add ( b, c ) );
    }

    protected TermFeature or(TermFeature a, TermFeature b) {
        return ifZero ( a, longTermConst ( 0 ), b );
    }

    protected TermFeature or(TermFeature a, TermFeature b, TermFeature c) {
        return or ( a, or ( b, c ) );
    }

    protected Feature or(Feature a, Feature b) {
        return ifZero ( a, longConst ( 0 ), b );
    }
    
    protected Feature or(Feature a, Feature b, Feature c) {
        return or ( a, or ( b, c ) );
    }
    
    protected Feature ifZero (Feature cond, Feature thenFeature) {
        return ShannonFeature.createConditionalBinary ( cond, thenFeature );
    }

    protected Feature ifZero (Feature cond, Feature thenFeature, Feature elseFeature) {
        return ShannonFeature.createConditionalBinary ( cond,
                                                        thenFeature,
                                                        elseFeature );
    }

    protected TermFeature ifZero (TermFeature cond, TermFeature thenFeature) {
        return ShannonTermFeature.createConditionalBinary ( cond, thenFeature );
    }

    protected TermFeature ifZero (TermFeature cond,
                                  TermFeature thenFeature,
                                  TermFeature elseFeature) {
        return ShannonTermFeature.createConditionalBinary ( cond,
                                                            thenFeature,
                                                            elseFeature );
    }

    protected Feature not(Feature f) {
        return ifZero ( f, inftyConst (), longConst ( 0 ) );
    }
    
    protected TermFeature not(TermFeature f) {
        return ifZero ( f,
                        ConstTermFeature.createConst(TopRuleAppCost.INSTANCE),
                        longTermConst(0) );
    }
    
    protected Feature eq(Feature a, Feature b) {
        return CompareCostsFeature.eq ( a, b );
    }
    
    protected Feature less(Feature a, Feature b) {
        return CompareCostsFeature.less ( a, b );
    }

    protected Feature leq(Feature a, Feature b) {
        return CompareCostsFeature.leq ( a, b );
    }

    /**
     * @param names
     * @param priority
     */
    protected Feature ifHeuristics (String[] names, int priority) {
        return ConditionalFeature.createConditional ( getFilterFor ( names ),
                c ( priority ), c ( 0 ) );
    }

    private RuleAppCost c (long p) {
        return LongRuleAppCost.create ( p );
    }

    private RuleAppCost infty () {
        return TopRuleAppCost.INSTANCE;
    }

    protected TacletFilter getFilterFor (String[] p_names) {
        ImmutableList<RuleSet> heur = ImmutableSLList.<RuleSet>nil();
        for ( int i = 0; i != p_names.length; ++i )
            heur = heur.prepend ( getHeuristic ( p_names[i] ) );
        return new IHTacletFilter ( false, heur );
    }

    protected RuleSet getHeuristic (String p_name) {
        final NamespaceSet nss = getProof ().getNamespaces ();
        
        assert nss != null : "Rule set namespace not available."; 
        
        final Namespace ns = nss.ruleSets ();
        final Named h = ns.lookup ( new Name ( p_name ) );
    
        assert h != null : "Did not find the rule set " + p_name;
    
        return (RuleSet)h;
    }

    protected void bindRuleSet(RuleSetDispatchFeature d,
                               RuleSet ruleSet, Feature f) {
        d.add ( ruleSet, f );
    }

    protected void bindRuleSet(RuleSetDispatchFeature d,
                               RuleSet ruleSet, long cost) {
        bindRuleSet ( d, ruleSet, longConst ( cost ) );
    }

    protected void bindRuleSet(RuleSetDispatchFeature d,
                               String ruleSet, Feature f) {
        bindRuleSet ( d, getHeuristic ( ruleSet ), f );
    }

    protected void bindRuleSet(RuleSetDispatchFeature d,
                               String ruleSet, long cost) {
        bindRuleSet ( d, getHeuristic ( ruleSet ), longConst ( cost ) );
    }

    protected void clearRuleSetBindings(RuleSetDispatchFeature d,
                                        RuleSet ruleSet) {
        d.clear ( ruleSet );
    }

    protected void clearRuleSetBindings(RuleSetDispatchFeature d,
                                        String ruleSet) {
        d.clear ( getHeuristic ( ruleSet ) );
    }

    /**
     * Create a projection of taclet applications to the instantiation of the
     * schema variables <code>schemaVar</code>. If <code>schemaVar</code>
     * is not instantiated for a particular taclet app, an error will be raised
     */
    protected ProjectionToTerm instOf(String schemaVar) {
        return SVInstantiationProjection.create ( new Name ( schemaVar ), true );
    }
    
    /**
     * Create a projection of taclet applications to the instantiation of the
     * schema variables <code>schemaVar</code>. The projection will be
     * partial and undefined for those taclet applications that do not
     * instantiate <code>schemaVar</code>
     */
    protected ProjectionToTerm instOfNonStrict(String schemaVar) {
        return SVInstantiationProjection.create ( new Name ( schemaVar ), false );
    }
    
    protected ProjectionToTerm subAt(ProjectionToTerm t, PosInTerm pit) {
        return SubtermProjection.create ( t, pit );
    }
    
    protected ProjectionToTerm sub(ProjectionToTerm t, int index) {
        return SubtermProjection.create ( t, PosInTerm.TOP_LEVEL.down ( index ) );
    }
    
    protected ProjectionToTerm opTerm(Operator op, ProjectionToTerm[] subTerms) {
        return TermConstructionProjection.create ( op, subTerms );
    }

    protected ProjectionToTerm opTerm(Operator op, ProjectionToTerm subTerm) {
        return opTerm ( op, new ProjectionToTerm[] { subTerm } );
    }

    protected ProjectionToTerm opTerm(Operator op,
                                      ProjectionToTerm subTerm0,
                                      ProjectionToTerm subTerm1) {
        return opTerm ( op, new ProjectionToTerm[] { subTerm0, subTerm1 } );
    }

    protected Feature isInstantiated(String schemaVar) {
        return InstantiatedSVFeature.create ( new Name ( schemaVar ) );
    }
    
    protected TermFeature op(Operator op) {
        return OperatorTF.create ( op );
    }

    protected TermFeature rec(TermFeature cond, TermFeature summand) {
        return RecSubTermFeature.create ( cond, summand );
    }
    
    protected TermFeature sub(TermFeature sub0) {
        return SubTermFeature.create ( new TermFeature[] { sub0 } );
    }
    
    protected TermFeature sub(TermFeature sub0, TermFeature sub1) {
        return SubTermFeature.create ( new TermFeature[] { sub0, sub1 } );
    }
    
    protected TermFeature opSub(Operator op, TermFeature sub0) {
        return add ( op ( op ), sub ( sub0 ) );
    }    
    
    protected TermFeature opSub(Operator op,
                                TermFeature sub0, TermFeature sub1) {
        return add ( op ( op ), sub ( sub0, sub1 ) );
    }    

    protected TermFeature eq(TermBuffer t) {
        return EqTermFeature.create ( t );
    }
    
    protected Feature eq(ProjectionToTerm t1, ProjectionToTerm t2) {
        final TermBuffer buf = new TermBuffer ();
        return let ( buf, t1, applyTF ( t2, eq ( buf ) ) );
    }

    protected Feature contains(ProjectionToTerm bigTerm,
                               ProjectionToTerm searchedTerm) {
        final TermBuffer buf = new TermBuffer ();
        return let ( buf, searchedTerm,
                     applyTF ( bigTerm,
                               not ( rec ( any (), not ( eq ( buf ) ) ) ) ) );
    }
    
    protected Feature println(ProjectionToTerm t) {
        return applyTF ( t, PrintTermFeature.INSTANCE );
    }
    
    protected TermFeature extendsTrans(Sort s) {
        return SortExtendsTransTermFeature.create ( s );
    }
    
    /**
     * Invoke the term feature <code>tf</code> on the term that instantiation
     * of <code>schemaVar</code>. This is the strict/safe version that raises an
     * error of <code>schemaVar</code> is not instantiated for a particular
     * taclet app
     */
    protected Feature applyTF(String schemaVar, TermFeature tf) {
        return applyTF ( instOf ( schemaVar ), tf );
    }

    /**
     * Invoke the term feature <code>tf</code> on the term that instantiation
     * of <code>schemaVar</code>. This is the non-strict/unsafe version that
     * simply returns zero if <code>schemaVar</code> is not instantiated for a
     * particular taclet app
     */
    protected Feature applyTFNonStrict(String schemaVar, TermFeature tf) {
        return applyTFNonStrict ( instOfNonStrict ( schemaVar ), tf );
    }

    /**
     * Evaluate the term feature <code>tf</code> for the term described by the
     * projection <code>term</code>. If <code>term</code> is undefined for
     * a particular rule app, an exception is raised
     */
    protected Feature applyTF(ProjectionToTerm term, TermFeature tf) {
        return ApplyTFFeature.create ( term, tf );
    }

    /**
     * Evaluate the term feature <code>tf</code> for the term described by the
     * projection <code>term</code>. If <code>term</code> is undefined for
     * a particular rule app, zero is returned
     */
    protected Feature applyTFNonStrict(ProjectionToTerm term, TermFeature tf) {
        return ApplyTFFeature.createNonStrict ( term, tf, LongRuleAppCost.ZERO_COST );
    }

    
    private final BackTrackingManager btManager = new BackTrackingManager ();
    
    protected BackTrackingManager getBtManager() {
        return btManager;
    }

    public final void instantiateApp ( RuleApp              app,
                                       PosInOccurrence      pio,
                                       Goal                 goal,
                                       RuleAppCostCollector collector ) {
        getBtManager ().setup ( app );
        do {
            final RuleAppCost cost = instantiateApp ( app, pio, goal );
            if ( cost instanceof TopRuleAppCost ) continue;
            final RuleApp res = getBtManager ().getResultingapp ();
            if ( res == app || res == null ) continue;
            collector.collect ( res, cost );
        } while ( getBtManager ().backtrack () );
    }
 
    protected abstract RuleAppCost instantiateApp (RuleApp              app,
                                                   PosInOccurrence      pio,
                                                   Goal                 goal);
    
    protected Feature forEach(TermBuffer x, TermGenerator gen, Feature body) {
        return ForEachCP.create ( x, gen, body, getBtManager () );
    }

    protected Feature oneOf(Feature[] features) {
        return OneOfCP.create ( features, getBtManager () );
    }
    
    protected Feature oneOf(Feature feature0, Feature feature1) {
        return oneOf ( new Feature[] { feature0, feature1 } );
    }
    
    protected Feature sum(TermBuffer x, TermGenerator gen, Feature body) {
        return ComprehendedSumFeature.create ( x, gen, body );
    }
    
    // it is possible to turn off the method <code>instantiate</code>,
    // which can be useful in order to use the same feature definitions both for
    // cost computation and instantiation
    
    private boolean instantiateActive = false;
    protected void enableInstantiate() {
        instantiateActive = true;
    }
    protected void disableInstantiate() {
        instantiateActive = false;
    }
    
    protected Feature instantiate(Name sv, ProjectionToTerm value) {
        if ( instantiateActive )
            return SVInstantiationCP.create ( sv, value, getBtManager () );
        else
            return longConst ( 0 );
    }
    
    protected Feature let(TermBuffer x, ProjectionToTerm value, Feature body) {
        return LetFeature.create ( x, value, body );
    }    
    
    protected Feature instantiate(String sv, ProjectionToTerm value) {
        return instantiate ( new Name ( sv ), value );
    }

    protected Feature isSubSortFeature(ProjectionToTerm s1, ProjectionToTerm s2) {        
        return SortComparisonFeature.create(s1, s2, SortComparisonFeature.SUBSORT);
    }
    
    protected Feature implicitCastNecessary(ProjectionToTerm s1) {
        return ImplicitCastNecessary.create(s1);
    }
    
}
