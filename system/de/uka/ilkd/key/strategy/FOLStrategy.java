// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;


import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.AssumptionProjection;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;


/**
 *
 */
public class FOLStrategy extends AbstractFeatureStrategy {
    
    private final Feature completeF;
    
    private final Feature approvalF;

    protected FOLStrategy ( Proof p_proof ) {
        super ( p_proof );

        final RuleSetDispatchFeature d = RuleSetDispatchFeature.create ();

        bindRuleSet ( d, "closure",  -9000 );
        bindRuleSet ( d, "concrete", -10000 );
        bindRuleSet ( d, "alpha",    -7000 );
        bindRuleSet ( d, "delta",    -6000 );
        bindRuleSet ( d, "pull_out_quantifier", 5000 );

        bindRuleSet ( d, "beta",
          add ( longConst ( -2500 ),
                ifZero ( SimplifyBetaCandidateFeature.INSTANCE,
                  SumFeature.createSum ( new Feature[] {
                    longConst ( -1070 ),
                    ifZero ( FocusHasConstraintFeature.INSTANCE, longConst ( 300 ) ),
                    ifZero ( PurePosDPathFeature.INSTANCE, longConst ( -200 ) ),
                    //	   ifZero ( ContainsQuantifierFeature.INSTANCE,
                    //		    longConst ( -2000 ) ),
                    ScaleFeature.createScaled ( CountPosDPathFeature.INSTANCE, -3.0 ),
                    ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 )
                  }) ) ) );

        final Feature introducedByGammaF = FormulaAddedByRuleFeature.create (
               getFilterFor ( new String[] { "gamma", "gamma_destructive" } ) );
        bindRuleSet ( d, "test_gen", inftyConst() );

        bindRuleSet ( d, "gamma",
                      ifZero ( introducedByGammaF,
                               longConst ( 0 ),
                               add ( ifZero ( NonDuplicateAppFeature.INSTANCE,
                                              longConst ( -200 ) ),
                                     longConst ( -3250 ) ) ) );

        bindRuleSet ( d, "gamma_destructive",
                      ifZero ( introducedByGammaF, longConst ( -5000 ) ) );

        final Feature replaceKnownF =
            SumFeature.createSum ( new Feature[] {
               SimplifyReplaceKnownCandidateFeature.INSTANCE,
               ifZero ( ConstraintStrengthenFeature.INSTANCE,
                        add ( ifZero ( SimplifyBetaCandidateFeature.INSTANCE,
                                       inftyConst () ),
			                  NotBelowQuantifierFeature.INSTANCE,
			                  LeftmostNegAtomFeature.INSTANCE ),
                        longConst ( -800 ) ),
               longConst ( -4000 ),
               ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 ) } );
        bindRuleSet ( d, "replace_known_left", replaceKnownF );
        bindRuleSet ( d, "replace_known_right", replaceKnownF );
        
        final TermBuffer equation = new TermBuffer ();
        bindRuleSet ( d, "apply_equations",
            add ( ifZero ( MatchedIfFeature.INSTANCE,
                           add ( CheckApplyEqFeature.INSTANCE,
                                 let ( equation,
                                       AssumptionProjection.create ( 0 ),
                                       TermSmallerThanFeature
                                       .create ( sub ( equation, 1 ),
                                                 sub ( equation, 0 ) ) ) ) ),
                  ifZero ( ConstraintStrengthenFeature.INSTANCE,
                           add ( ifZero ( SimplifyBetaCandidateFeature.INSTANCE,
                                          inftyConst () ), 
                                 NotBelowQuantifierFeature.INSTANCE,
                                 ifZero ( ContainsQuantifierFeature.INSTANCE,
                                          inftyConst () ) ) ),
                  longConst ( -4000 ) ) );
        
        bindRuleSet ( d, "order_terms",
           add ( TermSmallerThanFeature.create ( instOf ( "commEqLeft" ),
                                                 instOf ( "commEqRight" ) ),
                 longConst ( -8000 ) ) );
        
        bindRuleSet ( d, "simplify_literals",
                      ifZero ( ConstraintStrengthenFeature.INSTANCE,
                               longConst ( -4000 ),
                               longConst ( -8000 ) ) );
        
        bindRuleSet ( d, "try_apply_subst",
                      add ( EqNonDuplicateAppFeature.INSTANCE,
                            longConst ( -10000 ) ) );
        
        // delete cast
        bindRuleSet ( d, "cast_deletion",
                      ifZero( implicitCastNecessary(instOf("castedTerm")), 
                              longConst (-5000), inftyConst ()));
        

        // disallow simplification of polynomials and inequations here
        // (these rules need guidance that is not present in this strategy)
        bindRuleSet ( d, "polySimp_expand", inftyConst () );
        bindRuleSet ( d, "polySimp_directEquations", inftyConst () );
        bindRuleSet ( d, "polySimp_pullOutGcd", inftyConst () );
        bindRuleSet ( d, "polySimp_saturate", inftyConst () );
        bindRuleSet ( d, "polySimp_applyEq", inftyConst () );
        bindRuleSet ( d, "polySimp_applyEqRigid", inftyConst () );
        bindRuleSet ( d, "polySimp_leftNonUnit", inftyConst () );
        bindRuleSet ( d, "inEqSimp_expand", inftyConst () );
        bindRuleSet ( d, "inEqSimp_directInEquations", inftyConst () );
        bindRuleSet ( d, "inEqSimp_saturate", inftyConst () );
        bindRuleSet ( d, "inEqSimp_pullOutGcd", inftyConst () );
        bindRuleSet ( d, "inEqSimp_propagation", inftyConst () );
        bindRuleSet ( d, "inEqSimp_special_nonLin", inftyConst() );
        bindRuleSet ( d, "inEqSimp_nonLin", inftyConst() );
        bindRuleSet ( d, "inEqSimp_signCases", inftyConst() );
        bindRuleSet ( d, "polyDivision", inftyConst() );
        bindRuleSet ( d, "defOps_div", inftyConst() );
        bindRuleSet ( d, "system_invariant", inftyConst () );
        bindRuleSet ( d, "query_normalize", inftyConst () );
        bindRuleSet ( d, "cut_direct", inftyConst () );
        bindRuleSet ( d, "negationNormalForm", inftyConst() );
        bindRuleSet ( d, "moveQuantToLeft", inftyConst() );
        bindRuleSet ( d, "conjNormalForm", inftyConst () );
        bindRuleSet ( d, "apply_equations_andOr", inftyConst () );
        bindRuleSet ( d, "elimQuantifier", inftyConst () );
        bindRuleSet ( d, "distrQuantifier", inftyConst () );
        bindRuleSet ( d, "swapQuantifiers", inftyConst () );
        bindRuleSet ( d, "pullOutQuantifierAll", inftyConst () );
        bindRuleSet ( d, "pullOutQuantifierEx", inftyConst () );
        bindRuleSet ( d, "query_normalize_high_costs", inftyConst() );
        
        bindRuleSet ( d, "javaIntegerSemantics", -100 );

        
        final Feature simplifierF = selectSimplifier ( -10000 );

        final Feature duplicateF =
            ifZero ( NonDuplicateAppFeature.INSTANCE,
                     longConst ( 0 ),
                     ifHeuristics ( new String[] { "gamma", "gamma_destructive" },
                                    longConst ( 5 ), inftyConst() ) );

        final Feature ifMatchedF = ifZero ( MatchedIfFeature.INSTANCE, 
                longConst ( +1 ) );
        
        completeF = SumFeature.createSum ( new Feature[] {
            AutomatedRuleFeature.INSTANCE, NotWithinMVFeature.INSTANCE,
            simplifierF, duplicateF,
            ifMatchedF, d, AgeFeature.INSTANCE } );
            
        approvalF = duplicateF;
    }
    
    public Name name () {
        return new Name("FOLStrategy");
    }


    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     * 
     * @return the cost of the rule application expressed as a
     *         <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule
     *         shall not be applied at all (it is discarded by the strategy).
     */
    public RuleAppCost computeCost (RuleApp app, PosInOccurrence pio, Goal goal) {
        return completeF.compute ( app, pio, goal );
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is
     * called immediately before a rule is really applied
     * @return true iff the rule should be applied, false otherwise
     */
    public boolean isApprovedApp (RuleApp app, PosInOccurrence pio, Goal goal) {
        return !( approvalF.compute ( app, pio, goal ) instanceof TopRuleAppCost );
    }
    
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return TopRuleAppCost.INSTANCE;
    }    

    public static class Factory extends StrategyFactory {
        public Factory () {
            
        }
        
        public Strategy create ( Proof p_proof, 
                StrategyProperties strategyProperties ) {
            return new FOLStrategy ( p_proof );
        }
        
        public Name name () {
            return new Name("FOLStrategy");
        }
    }
}
