// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.feature.*;


/**
 *
 */
public class SimpleFOLStrategy extends AbstractFeatureStrategy {
    
    public static final Name NAME = new Name ( "Simple FOL" );
    
    private final Feature closureF;
    private final Feature concreteF;
    private final Feature alphaF;
    private final Feature betaF;
    private final Feature gammaF;
    private final Feature gammaDestructiveF;
    private final Feature deltaF;
    private final Feature pullOutQuantifierF;
    private final Feature replaceKnownF;
    private final Feature applyEquationsF;
    private final Feature orderTermsF;
    private final Feature simplifierF;
    private final Feature literalsF;
    private final Feature duplicateF;
    private final Feature ifMatchedF;
    
    private final Feature introducedByGammaF;
    
    private final Feature completeF;
    
    private final Feature approvalF;

    protected SimpleFOLStrategy ( Proof p_proof ) {
        super ( p_proof );
        
        closureF  = ifHeuristics ( new String[] { "closure" },  -9000 );
        concreteF = ifHeuristics ( new String[] { "concrete" }, -10000 );
        alphaF    = ifHeuristics ( new String[] { "alpha" },    -7000 );
        deltaF    = ifHeuristics ( new String[] { "delta" },    -6000 );
        pullOutQuantifierF = ifHeuristics ( new String[] { "pull_out_quantifier" }, 5000 );

        betaF = ifHeuristics ( new String[] { "beta" },
   add ( longConst ( -2500 ),
	 ifZero ( SimplifyBetaCandidateFeature.INSTANCE,
		  SumFeature.createSum ( new Feature[] {
		      longConst ( -1070 ),
		      ifZero ( PurePosDPathFeature.INSTANCE,
			       longConst ( -200 ) ),
		      //		      ifZero ( ContainsQuantifierFeature.INSTANCE,
		      //			       longConst ( -2000 ) ),
		      ScaleFeature.createScaled ( CountPosDPathFeature.INSTANCE, -3.0 ),
		      ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 )
		  } ) ) ) );

        introducedByGammaF = FormulaAddedByRuleFeature.create (
               getFilterFor ( new String[] { "gamma", "gamma_destructive" } ) );

        gammaF = ifHeuristics ( new String [] { "gamma" },
                                ifZero ( introducedByGammaF,
                                         longConst ( 0 ),
                                         add ( ifZero ( NonDuplicateAppFeature.INSTANCE,
                                                        longConst ( -200 ) ),
                                               longConst ( -3250 ) ) ) );

        gammaDestructiveF = ifHeuristics ( new String[] { "gamma_destructive" },
                                           ifZero ( introducedByGammaF,
                                                    longConst ( -5000 ) ) );

        replaceKnownF = ifHeuristics 
         ( new String[] { "replace_known" },
           SumFeature.createSum ( new Feature[] {
               SimplifyReplaceKnownCandidateFeature.INSTANCE,
               ifZero ( ConstraintStrengthenFeature.INSTANCE,
                        SumFeature.createSum ( new Feature[] {
			    ifZero ( SimplifyBetaCandidateFeature.INSTANCE,
				     inftyConst () ),
			    NotBelowQuantifierFeature.INSTANCE,
			    LeftmostNegAtomFeature.INSTANCE } ),
                        longConst ( -800 ) ),
               longConst ( -4000 ),
               ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE,
                                           10.0 ) } ) );
        
        applyEquationsF = ifHeuristics 
       ( new String [] { "apply_equations" },
         SumFeature.createSum ( new Feature [] {
                 ifZero ( MatchedIfFeature.INSTANCE,
                          //add (
                               CheckApplyEqFeature.INSTANCE
                          //     ,
                          //      OrderingFeature.INSTANCE
                          //      )
                                ),
                 ifZero ( ConstraintStrengthenFeature.INSTANCE,
                          SumFeature.createSum ( new Feature [] {
                                  ifZero ( SimplifyBetaCandidateFeature.INSTANCE,
                                           inftyConst () ),
                                  NotBelowQuantifierFeature.INSTANCE,
                                  ifZero ( ContainsQuantifierFeature.INSTANCE,
                                           inftyConst () ) } ) ),
                 longConst ( -4000 ) } ) );
        
        orderTermsF = ifHeuristics ( new String[] { "order_terms" },
                                     inftyConst() );
//                                     add ( OrderingFeature.INSTANCE,
//                                           longConst ( -8000 ) ) );
        
        literalsF = ifHeuristics ( new String [] { "simplify_literals" },
                                   ifZero ( ConstraintStrengthenFeature.INSTANCE,
                                            longConst ( -4000 ),
                                            longConst ( -8000 ) ) );
        
        simplifierF = selectSimplifier ( -10000 );

        duplicateF = ifHeuristics ( new String[] { "gamma", "gamma_destructive" },
                                    longConst ( 0 ),
                                    NonDuplicateAppFeature.INSTANCE );

        ifMatchedF = ifZero ( MatchedIfFeature.INSTANCE, longConst ( +1 ) );
        
        completeF = SumFeature.createSum ( new Feature[] { AgeFeature.INSTANCE,
            AutomatedRuleFeature.INSTANCE, closureF, concreteF, alphaF, betaF,
            gammaF, gammaDestructiveF, deltaF, replaceKnownF, applyEquationsF,
            orderTermsF, simplifierF, literalsF, duplicateF, pullOutQuantifierF,
            ifMatchedF } );
            
        approvalF = duplicateF;
    }
    
    public Name name () {
        return NAME;
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
        public Strategy create ( Proof p_proof, StrategyProperties properties ) {
            return new SimpleFOLStrategy ( p_proof );
        }
        
        public Name name () {
            return NAME;
        }
    }
}
