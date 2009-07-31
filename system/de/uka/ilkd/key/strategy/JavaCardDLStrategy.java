// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.strategy;

import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.ClassRuleFilter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.SetRuleFilter;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.smt.SMTRule;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.quantifierHeuristics.*;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.*;
import de.uka.ilkd.key.strategy.termgenerator.*;


/**
 * Strategy tailored to be used as long as a java program can be found in
 * the sequent.
 */
public class JavaCardDLStrategy extends AbstractFeatureStrategy {

    private final RuleSetDispatchFeature costComputationDispatcher;
    private final Feature costComputationF;
    private final RuleSetDispatchFeature approvalDispatcher;
    private final Feature approvalF;
    private final RuleSetDispatchFeature instantiationDispatcher;
    private final Feature instantiationF;
    
    protected final RuleSetDispatchFeature getCostComputationDispatcher() {
        return costComputationDispatcher;
    }

    protected final RuleSetDispatchFeature getInstantiationDispatcher() {
        return instantiationDispatcher;
    }

    private final StrategyProperties strategyProperties;
    
    protected JavaCardDLStrategy(Proof p_proof,
                                 StrategyProperties strategyProperties) {
        
        super ( p_proof );
        
        this.strategyProperties =
            (StrategyProperties)strategyProperties.clone ();
        
        this.tf = new ArithTermFeatures ( p_proof.getServices ()
                                          .getTypeConverter ().getIntegerLDT () );
        this.ff = new FormulaTermFeatures ();        
        
        costComputationDispatcher = setupCostComputationF ( p_proof );
        approvalDispatcher = setupApprovalDispatcher ( p_proof );
        instantiationDispatcher = setupInstantiationF ( p_proof );
        
        costComputationF = setupGlobalF ( costComputationDispatcher, p_proof );
        instantiationF = setupGlobalF ( instantiationDispatcher, p_proof );
        approvalF = add ( setupApprovalF ( p_proof ), approvalDispatcher );
    }

    private Feature setupGlobalF(Feature dispatcher, Proof p_proof) {
//        final Feature simplifierF = selectSimplifier ( -10000 );
//        
        final Feature ifMatchedF = ifZero ( MatchedIfFeature.INSTANCE,
                                            longConst ( +1 ) );
    
//        final Feature splitF =
//            ScaleFeature.createScaled ( CountBranchFeature.INSTANCE, 400);
        final Feature ifThenElseF =
            ScaleFeature.createScaled ( IfThenElseMalusFeature.INSTANCE, 500);
    
        final Feature strengthenConstraints =
            ifHeuristics ( new String[] { "concrete", "closure" },
                           longConst ( 0 ),
                           ifZero ( ConstraintStrengthenFeatureUC.create ( p_proof ),
                                    inftyConst () ) );
    
            
        final Feature methodSpecF;
        final String methProp 
        	= strategyProperties.getProperty(
        		StrategyProperties.METHOD_OPTIONS_KEY);        
        if (methProp.equals(StrategyProperties.METHOD_CONTRACT)) {   
            methodSpecF = methodSpecFeature(longConst(-20));
        } else if (methProp.equals(StrategyProperties.METHOD_EXPAND)) {  
            methodSpecF = methodSpecFeature(inftyConst());
        } else if (methProp.equals(StrategyProperties.METHOD_NONE)) {   
            methodSpecF = methodSpecFeature(inftyConst());
        } else {
            methodSpecF = null;
            assert false;
        }
            
        
        final Feature oneStepSimplificationF 
        	= oneStepSimplificationFeature(longConst(-10000));
        
        
        final Feature smtF = smtFeature(inftyConst());

        return SumFeature.createSum ( new Feature [] {
              AutomatedRuleFeature.INSTANCE,
//              splitF,
              dispatcher,
              NonDuplicateAppFeature.INSTANCE,
              strengthenConstraints, 
              AgeFeature.INSTANCE,
              oneStepSimplificationF,
              smtF,
              methodSpecF, 
              ifMatchedF,
              ifThenElseF } );
    }

    private Feature methodSpecFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(UseOperationContractRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);        
    }
    
    private Feature oneStepSimplificationFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(OneStepSimplifier.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);        
    } 
    
    private Feature smtFeature(Feature cost) {
	ClassRuleFilter filter = new ClassRuleFilter(SMTRule.class);
        return ConditionalFeature.createConditional(filter, cost);        
    }       
    

    
    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the computation of costs for taclet applications
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    
    private RuleSetDispatchFeature setupCostComputationF(Proof p_proof) {
        final IntegerLDT numbers =
            p_proof.getServices().getTypeConverter().getIntegerLDT();
            
        final RuleSetDispatchFeature d = RuleSetDispatchFeature.create ();
            
        bindRuleSet ( d, "closure", -9000 );
        bindRuleSet ( d, "concrete", -10000 );
        bindRuleSet ( d, "alpha", -7000 );
        bindRuleSet ( d, "delta", -6000 );
            
        bindRuleSet ( d, "simplify_boolean", -200 );
        bindRuleSet ( d, "simplify", -200 );
        bindRuleSet ( d, "simplify_expression", -100 );
        bindRuleSet ( d, "executeIntegerAssignment", -100 );

        bindRuleSet ( d, "javaIntegerSemantics", -5000 );
            
        setupSplitting ( d );

        bindRuleSet ( d, "test_gen", inftyConst () );

        bindRuleSet ( d, "gamma",
                      add ( not ( isInstantiated ( "t" ) ),
                            ifZero ( allowQuantifierSplitting (),
                                     longConst ( 0 ), longConst ( 50 ) ) ) );
        bindRuleSet ( d, "gamma_destructive", inftyConst () );

        setupReplaceKnown ( d );        
            
        bindRuleSet ( d, "confluence_restricted",
                      ifZero ( MatchedIfFeature.INSTANCE,
                               DiffFindAndIfFeature.INSTANCE ) );
        
        setupApplyEq ( d, numbers );

        bindRuleSet ( d, "insert_eq_nonrigid",
                      applyTF ( FocusProjection.create ( 0 ),
                                IsNonRigidTermFeature.INSTANCE ) );
        
        bindRuleSet ( d, "order_terms",
           add ( ifZero (
                   applyTF ( "commEqLeft", tf.intF ),
                   add ( applyTF ( "commEqRight", tf.monomial ),
                         applyTF ( "commEqLeft", tf.polynomial ),
                         monSmallerThan ( "commEqLeft", "commEqRight", numbers ) ),
                   termSmallerThan ( "commEqLeft", "commEqRight" ) ),
                   longConst ( -5000 ) ) );
        
        bindRuleSet ( d, "simplify_literals",
                      ifZero ( ConstraintStrengthenFeatureUC.create(p_proof),
                               longConst ( 0 ),
                               longConst ( -8000 ) ) );
        
        bindRuleSet ( d, "simplify_instanceof_static",
                      add ( EqNonDuplicateAppFeature.INSTANCE,
                            longConst ( -500 ) ) );

        bindRuleSet ( d, "comprehensions",
                      add ( NonDuplicateAppModPositionFeature.INSTANCE,
                            longConst ( 1000 ) ) );
        
        bindRuleSet ( d, "comprehensions_high_costs",
                add ( NonDuplicateAppModPositionFeature.INSTANCE,
                      longConst ( 10000 ) ) );

        bindRuleSet ( d, "comprehensions_low_costs",
                add ( NonDuplicateAppModPositionFeature.INSTANCE,
                      longConst ( -5000 ) ) );
        
        bindRuleSet ( d, "evaluate_instanceof", longConst ( -500 ) );
        
        bindRuleSet ( d, "instanceof_to_exists", TopLevelFindFeature.ANTEC );
        
        bindRuleSet ( d, "try_apply_subst",
                      add ( EqNonDuplicateAppFeature.INSTANCE,
                            longConst ( -10000 ) ) );
        
        final TermBuffer superFor = new TermBuffer ();
        bindRuleSet ( d, "split_if",
           add ( sum ( superFor, SuperTermGenerator.upwards ( any () ),
                       applyTF ( superFor, not ( ff.program ) ) ),
                 longConst ( 50 ) ) );
        
        final String[] exceptionsWithPenalty = new String[]{
                    "java.lang.NullPointerException",
                    "java.lang.ArrayIndexOutOfBoundsException",
                    "java.lang.ArrayStoreException",
                    "java.lang.ClassCastException"                
        };
            
        bindRuleSet ( d, "simplify_prog",
           ifZero ( ThrownExceptionFeature.create( exceptionsWithPenalty, 
                                                   p_proof.getServices() ),
                    longConst ( 500 ),
                    ifZero ( isBelow ( add ( ff.forF, not ( ff.atom ) ) ),
                             longConst ( 200 ), longConst ( -100 ) ) ) );
                
        
        // features influenced by the strategy options
        
        boolean useLoopExpand = strategyProperties.getProperty(
                StrategyProperties.LOOP_OPTIONS_KEY).
                    equals(StrategyProperties.LOOP_EXPAND);
        boolean useLoopInvariant = strategyProperties.getProperty(
                StrategyProperties.LOOP_OPTIONS_KEY).
                    equals(StrategyProperties.LOOP_INVARIANT);
        boolean programsToRight = expandQueries () ||
                strategyProperties.getProperty(
                StrategyProperties.QUERY_OPTIONS_KEY).
                    equals(StrategyProperties.QUERY_PROGRAMS_TO_RIGHT);
        
        String methProp =
            strategyProperties.getProperty ( StrategyProperties.METHOD_OPTIONS_KEY );
	
        if (methProp.equals(StrategyProperties.METHOD_CONTRACT)) {
            bindRuleSet(d, "method_expand", longConst(100));	
        } else if (methProp.equals(StrategyProperties.METHOD_EXPAND)) {
            bindRuleSet(d, "method_expand", longConst(100));	   
        } else if (methProp.equals(StrategyProperties.METHOD_NONE)) {
            bindRuleSet(d, "method_expand", inftyConst());	  
        } else throw new RuntimeException("Unexpected strategy property "+
                                          methProp);
	
        
        bindRuleSet ( d, "loop_expand",
                      useLoopExpand ? longConst ( 0 )
                                    : inftyConst () );
        
        bindRuleSet  ( d, "loop_invariant", 
                       useLoopInvariant ? longConst ( 100 )  
                                        : inftyConst () );
            
        bindRuleSet  ( d, "loop_invariant_proposal", 
                       ifHeuristics(new String[]{"loop_invariant"}, 
                                    longConst(0), inftyConst()));
            
        // delete cast
        bindRuleSet ( d, "cast_deletion",
                      ifZero ( implicitCastNecessary ( instOf ( "castedTerm" ) ),
                               longConst ( -5000 ), inftyConst () ) );
           
        setupQueries ( d );
            
        bindRuleSet ( d, "inReachableStateImplication",
                      add ( NonDuplicateAppModPositionFeature.INSTANCE,
                            longConst ( 100 ) ) );

        bindRuleSet ( d, "inReachableStateExpandAntec", -200 );

        bindRuleSet ( d, "inReachableStateExpandRewrite",
		      add ( not ( TopLevelFindFeature.ANTEC ),
		            NonDuplicateAppModPositionFeature.INSTANCE,
		            longConst ( -100 ) ) );

        bindRuleSet ( d, "type_hierarchy_def", -6500 );
        
        if ( programsToRight )
            bindRuleSet ( d, "boxDiamondConv",
                          TopLevelFindFeature.ANTEC_WITH_UPDATE );
        else
            bindRuleSet ( d, "boxDiamondConv", inftyConst () );
        
        bindRuleSet ( d, "cut", not ( isInstantiated ( "cutFormula" ) ) );
        
        setupUserTaclets ( d );
        
        setupArithPrimaryCategories ( d );
        setupPolySimp ( d, numbers );        
        setupInEqSimp ( d, p_proof, numbers );
        
        setupDefOpsPrimaryCategories ( d );
        
        setupSystemInvariantSimp(d);

        if ( quantifierInstantiatedEnabled() ) {
            setupFormulaNormalisation ( d, numbers );
        } else {
            bindRuleSet ( d, "negationNormalForm", inftyConst() );
            bindRuleSet ( d, "moveQuantToLeft", inftyConst() );
            bindRuleSet ( d, "conjNormalForm", inftyConst () );
            bindRuleSet ( d, "apply_equations_andOr", inftyConst () );
            bindRuleSet ( d, "elimQuantifier", inftyConst () );
            bindRuleSet ( d, "distrQuantifier", inftyConst () );
            bindRuleSet ( d, "swapQuantifiers", inftyConst () );
            bindRuleSet ( d, "pullOutQuantifierAll", inftyConst () );
            bindRuleSet ( d, "pullOutQuantifierEx", inftyConst () );
        }

        // For taclets that need instantiation, but where the instantiation is
        // deterministic and does not have to be repeated at a later point, we
        // setup the same feature terms as in the instantiation method. The
        // definitions in <code>setupInstantiationWithoutRetry</code> should
        // give cost infinity to those incomplete rule applications that will
        // never be instantiated (so that these applications can be removed from
        // the queue and do not have to be considered again).
        setupInstantiationWithoutRetry ( d, p_proof );
        
        return d;
    }

    private void setupReplaceKnown(RuleSetDispatchFeature d) {
        final Feature commonF =
            add ( ifZero ( MatchedIfFeature.INSTANCE,
                           DiffFindAndIfFeature.INSTANCE ),
                  longConst ( -5000 ),
                  ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 ) );

        bindRuleSet ( d, "replace_known_left", commonF );
        bindRuleSet ( d, "replace_known_right",
            add ( commonF,
                  ifZero ( DirectlyBelowSymbolFeature.create ( Junctor.IMP, 1 ),
                           longConst ( 100 ),
                  ifZero ( DirectlyBelowSymbolFeature.create ( Equality.EQV ),
                           longConst ( 100 ) ) ) ) );
    }

    private void setupQueries(RuleSetDispatchFeature d) {
        // attention: usually this application is against the term order but
        // does not interfere as only applied below updates
        bindRuleSet ( d, "query_normalize", 
	    SumFeature.createSum ( new Feature [] {
                DirectlyBelowOpClassFeature.create ( ProgramMethod.class ),
                applyTF(FocusProjection.create(2), ff.update),
                applyTF("t", IsNonRigidTermFeature.INSTANCE),
		// we actually have to be in the scope of an update,
		// not only within an update
		not(NotInScopeOfModalityFeature.INSTANCE),
                longConst (-10) } ));

        bindRuleSet ( d, "query_normalize_high_costs", 
	    SumFeature.createSum ( new Feature [] {
                SomeWhereBelowOpClassFeature.create ( ProgramMethod.class ),
                SomeWhereBelowOpClassFeature.create ( UpdateApplication.class ),
                applyTF("t", IsNonRigidTermFeature.INSTANCE),
		// we actually have to be in the scope of an update,
		// not only within an update
		not(NotInScopeOfModalityFeature.INSTANCE),
                longConst (10) } ));

        if ( expandQueries () )
            bindRuleSet ( d, "queries",
                add ( normalSplitting () ?
                         not ( isBelow ( add ( ff.forF, not ( ff.atom ) ) ) ) :
                         longConst ( 0 ),
                      NonDuplicateAppModPositionFeature.INSTANCE ) );
        else
            bindRuleSet ( d, "queries", inftyConst () );
    }

    private void setupUserTaclets(RuleSetDispatchFeature d) {
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            final String userTacletsProbs =
                strategyProperties.getProperty ( StrategyProperties.USER_TACLETS_OPTIONS_KEY(i) );
            if ( StrategyProperties.USER_TACLETS_LOW.equals ( userTacletsProbs ) )
                bindRuleSet ( d, "userTaclets" + i, 10000 );
            else if ( StrategyProperties.USER_TACLETS_HIGH.equals ( userTacletsProbs ) )
                bindRuleSet ( d, "userTaclets" + i, -50 );
            else 
                bindRuleSet ( d, "userTaclets" + i, inftyConst() );
        }
    }

    private void setupSystemInvariantSimp(RuleSetDispatchFeature d) {
        bindRuleSet ( d, "system_invariant", 
           ifZero ( MatchedIfFeature.INSTANCE,
                    add ( applyTF ( "negLit", tf.negLiteral ),
                          applyTFNonStrict ( "nonNegLit", tf.nonNegLiteral ) ) ) );
    }
    
    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Queries for the active taclet options
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    
    private boolean expandQueries() {
        return strategyProperties.getProperty(
                StrategyProperties.QUERY_OPTIONS_KEY).
                    equals(StrategyProperties.QUERY_EXPAND);
    }

    private boolean arithNonLinInferences() {
        return StrategyProperties.NON_LIN_ARITH_COMPLETION.equals (
                 strategyProperties.getProperty
                 ( StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY ) );
    }

    protected boolean arithDefOps() {
        return
          StrategyProperties.NON_LIN_ARITH_DEF_OPS.equals (
            strategyProperties.getProperty
            ( StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY ) )
          ||
          StrategyProperties.NON_LIN_ARITH_COMPLETION.equals (
            strategyProperties.getProperty
            ( StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY ) );
    }

    private boolean instQuantifiersWithQueries() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
               .equals ( strategyProperties.getProperty
                         ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) );
    }
    
    private boolean quantifiersMightSplit() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
               .equals ( strategyProperties.getProperty
                         ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) )
               ||
               StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS
               .equals ( strategyProperties.getProperty
                         ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) );
    }
    
    private Feature allowQuantifierSplitting() {
        if ( StrategyProperties.QUANTIFIERS_INSTANTIATE
             .equals ( strategyProperties.getProperty
                       ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) ) )
            return longConst ( 0 );
        if ( StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS
             .equals ( strategyProperties.getProperty
                       ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) ) )
            return sequentContainsNoPrograms ();
        return inftyConst ();
    }

    private Feature sequentContainsNoPrograms() {
//        return not ( expandQueries ()
//                     ? SeqContainsExecutableCodeFeature.PROGRAMS_OR_QUERIES
//                     : SeqContainsExecutableCodeFeature.PROGRAMS );
        return not ( SeqContainsExecutableCodeFeature.PROGRAMS );
    }
    
    private boolean quantifierInstantiatedEnabled () {
        return !StrategyProperties.QUANTIFIERS_NONE.equals (
                 strategyProperties.getProperty
                 ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) );
    }

    private Feature allowSplitting(ProjectionToTerm focus) {
        if ( normalSplitting () ) return longConst ( 0 );
        
        if ( StrategyProperties.SPLITTING_DELAYED
                .equals ( strategyProperties.getProperty
                          ( StrategyProperties.SPLITTING_OPTIONS_KEY ) ) )        
            return or ( applyTF ( focus,
                                  ContainsExecutableCodeTermFeature.PROGRAMS ),
                        sequentContainsNoPrograms () );

        // else: SPLITTING_OFF
        return applyTF ( focus, ContainsExecutableCodeTermFeature.PROGRAMS );
    }

    private boolean normalSplitting() {
        return StrategyProperties.SPLITTING_NORMAL
                .equals ( strategyProperties.getProperty
                          ( StrategyProperties.SPLITTING_OPTIONS_KEY ) );
    }


    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Application of beta- and cut-rules to handle disjunctions
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private void setupSplitting(RuleSetDispatchFeature d) {
        final TermBuffer subFor = new TermBuffer ();
        final Feature noCutsAllowed =
            sum ( subFor, AllowedCutPositionsGenerator.INSTANCE,
                  not ( applyTF ( subFor, ff.cutAllowed ) ) );
        
        bindRuleSet ( d, "beta",
          SumFeature.createSum ( new Feature [] {
             noCutsAllowed,
             ifZero ( PurePosDPathFeature.INSTANCE, longConst ( -200 ) ),
             ScaleFeature.createScaled ( CountPosDPathFeature.INSTANCE, -3.0 ),
             ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 ),
             longConst ( 20 )
          } ) );

        bindRuleSet ( d, "split_cond", longConst ( 1 ) );

        bindRuleSet ( d, "cut_direct",
           SumFeature.createSum ( new Feature [] {
             not ( TopLevelFindFeature.ANTEC_OR_SUCC_WITH_UPDATE ),
             AllowedCutPositionFeature.INSTANCE,
             ifZero ( NotBelowQuantifierFeature.INSTANCE,
                      add ( applyTF ( "cutFormula", ff.cutAllowed ),
                            longConst ( 10 ) ),
                      SumFeature.createSum ( new Feature [] {
                            applyTF ( "cutFormula",
                                      ff.cutAllowedBelowQuantifier ),
                            applyTF ( FocusFormulaProjection.INSTANCE,
                                      ff.quantifiedClauseSet ),
                            ifZero ( allowQuantifierSplitting (),
                                     longConst ( 0 ), longConst ( 100 ) ) } ) ) } ) );
    }

    private void setupSplittingApproval(RuleSetDispatchFeature d) {
        bindRuleSet ( d, "beta",
                      allowSplitting ( FocusFormulaProjection.INSTANCE ) );

        bindRuleSet ( d, "split_cond",
                      allowSplitting ( FocusProjection.create ( 0 ) ) );

        final TermBuffer subFor = new TermBuffer ();
        final Feature compareCutAllowed =
            ifZero ( applyTF ( subFor, ff.cutAllowed ),
                     leq ( applyTF ( "cutFormula", ff.cutPriority ),
                           applyTF ( subFor, ff.cutPriority ) ) );

        final Feature noBetterCut =
            sum ( subFor, AllowedCutPositionsGenerator.INSTANCE, compareCutAllowed );

        bindRuleSet ( d, "cut_direct",
             add ( allowSplitting ( FocusFormulaProjection.INSTANCE ),
                   ifZero ( NotBelowQuantifierFeature.INSTANCE,
                            noBetterCut ) ) );
    }

    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Application of equations
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private void setupApplyEq(RuleSetDispatchFeature d, IntegerLDT numbers) {
        final TermBuffer equation = new TermBuffer ();
        final TermBuffer left = new TermBuffer (), right = new TermBuffer ();

        // applying equations less deep/less leftish in terms/formulas is preferred
        // this is important for reducing polynomials (start with the biggest
        // summands)
        bindRuleSet ( d, "apply_equations",
           SumFeature.createSum ( new Feature[] {
                 ifZero ( applyTF ( FocusProjection.create ( 0 ), tf.intF ),
                          add ( applyTF ( FocusProjection.create ( 0 ),
                                          tf.monomial ),
                                ScaleFeature.createScaled
                                ( FindRightishFeature.create ( numbers ), 5.0 ) ) ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   add (
                   CheckApplyEqFeature.INSTANCE,
                   let ( equation, AssumptionProjection.create ( 0 ),
                         add ( not ( applyTF ( equation, ff.update ) ),
                         // there might be updates in front of the assumption
                         // formula; in this case we wait until the updates have
                         // been applied
                   let ( left, sub ( equation, 0 ),
                   let ( right, sub ( equation, 1 ),
                         ifZero ( applyTF ( left, tf.intF ),
                                  add ( applyTF ( left, tf.nonNegOrNonCoeffMonomial ),
                                        applyTF ( right, tf.polynomial ),
                                        MonomialsSmallerThanFeature
                                        .create ( right, left, numbers ) ),
                                  TermSmallerThanFeature.create ( right, left ) )
                            ) ) ) ) ) ),
                 longConst ( -4000 ) } ) );
    }

    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Normalisation of formulas; this is mostly a pre-processing step for
    // handling quantified formulas
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private void setupFormulaNormalisation(RuleSetDispatchFeature d,
                                           IntegerLDT numbers) {
       
        bindRuleSet ( d, "negationNormalForm",
           add ( not ( NotBelowBinderFeature.INSTANCE ),
                 longConst ( -500 ),
                 ScaleFeature.createScaled ( FindDepthFeature.INSTANCE, 10.0 ) ) );

        bindRuleSet ( d, "moveQuantToLeft",
           add ( quantifiersMightSplit () ?
                      longConst ( 0 ) :
                      applyTF ( FocusFormulaProjection.INSTANCE,
                                ff.quantifiedPureLitConjDisj ),
                 longConst ( -550 ) ) );

        bindRuleSet ( d, "conjNormalForm",
                      add ( not ( applyTF ( FocusFormulaProjection.INSTANCE,
                                            ff.propJunctor ) ),
                            NotInScopeOfModalityFeature.INSTANCE,
                            longConst ( -150 ) ) );

        bindRuleSet ( d, "elimQuantifier", -1000 );
        bindRuleSet ( d, "elimQuantifierWithCast", 50 );

        final TermBuffer left = new TermBuffer ();
        final TermBuffer right = new TermBuffer ();
        bindRuleSet ( d, "apply_equations_andOr",
           add ( let ( left, instOf ( "applyEqLeft" ),
                 let ( right, instOf ( "applyEqRight" ),
                 ifZero ( applyTF ( left, tf.intF ),
                          add ( applyTF ( left, tf.nonNegOrNonCoeffMonomial ),
                                applyTF ( right, tf.polynomial ),
                                MonomialsSmallerThanFeature
                                .create ( right, left, numbers ) ),
                           TermSmallerThanFeature.create ( right, left ) ) ) ),
                 longConst ( -150 ) ) );
        
        bindRuleSet ( d, "distrQuantifier",
           add ( or ( applyTF ( FocusProjection.create ( 0 ),
                                add ( ff.quantifiedClauseSet,
				      not ( opSub ( Quantifier.ALL, ff.orF ) ),
                                      EliminableQuantifierTF.INSTANCE ) ),
                      SumFeature.createSum ( new Feature[] {
                           OnlyInScopeOfQuantifiersFeature.INSTANCE,
                           SplittableQuantifiedFormulaFeature.INSTANCE,
                           ifZero ( FocusInAntecFeature.INSTANCE,
                                    applyTF ( FocusProjection.create ( 0 ),
                                              sub ( ff.andF ) ),
                                    applyTF ( FocusProjection.create ( 0 ),
                                              sub ( ff.orF ) ) ) } ) ),
                 longConst ( -300 ) ) );

        bindRuleSet ( d, "swapQuantifiers",
           add ( applyTF ( FocusProjection.create ( 0 ),
                           add ( ff.quantifiedClauseSet,
                                 EliminableQuantifierTF.INSTANCE,
                                 sub ( not ( EliminableQuantifierTF.INSTANCE ) ) ) ),
                 longConst ( -300 ) ) );

        
        // category "conjunctive normal form"
        
        bindRuleSet ( d, "cnf_orComm",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "commRight", ff.clause ),
             applyTFNonStrict ( "commResidue", ff.clauseSet ),
             or ( applyTF ( "commLeft", ff.andF ),
                  add ( applyTF ( "commLeft", ff.literal ),
                        literalsSmallerThan ( "commRight", "commLeft", numbers ) ) ),
             longConst ( -100 ) } ) );

        bindRuleSet ( d, "cnf_orAssoc",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "assoc0", ff.clause ),
             applyTF ( "assoc1", ff.clause ),
             applyTF ( "assoc2", ff.literal ),
             longConst ( -80 ) } ) );

        bindRuleSet ( d, "cnf_andComm",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "commLeft", ff.clause ),
             applyTF ( "commRight", ff.clauseSet ),
             applyTFNonStrict ( "commResidue", ff.clauseSet ),
             // at least one of the subformulas has to be a literal; otherwise,
             // sorting is not likely to have any big effect
             ifZero ( add ( applyTF ( "commLeft", not ( ff.literal ) ),
                            applyTF ( "commRight",
                                      rec ( ff.andF, not ( ff.literal ) ) ) ),
                      longConst ( 100 ),
		      longConst ( -60 ) ),
             clausesSmallerThan ( "commRight", "commLeft", numbers ) } ) );

        bindRuleSet ( d, "cnf_andAssoc",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "assoc0", ff.clauseSet ),
             applyTF ( "assoc1", ff.clauseSet ),
             applyTF ( "assoc2", ff.clause ),
             longConst ( -10 ) } ) );

        bindRuleSet ( d, "cnf_dist",
           SumFeature.createSum( new Feature[] {
             applyTF ( "distRight0", ff.clauseSet ),
             applyTF ( "distRight1", ff.clauseSet ),
             ifZero ( applyTF ( "distLeft", ff.clause ),
                      longConst ( -15 ),
                      applyTF ( "distLeft", ff.clauseSet ) ),
             longConst ( -35 ) } ) );

        final TermBuffer superFor = new TermBuffer ();
        final Feature onlyBelowQuanAndOr =
            sum ( superFor, SuperTermGenerator.upwards ( any () ),
                  applyTF ( superFor,
                            or ( ff.quantifiedFor, ff.andF, ff.orF ) ) );
        
        final Feature belowUnskolemisableQuantifier =
            ifZero ( FocusInAntecFeature.INSTANCE,
              not ( sum ( superFor,
                          SuperTermGenerator.upwards ( any () ),
                          not ( applyTF ( superFor, op ( Quantifier.ALL ) ) ) ) ),
              not ( sum ( superFor,
                          SuperTermGenerator.upwards ( any () ),
                          not ( applyTF ( superFor, op ( Quantifier.EX ) ) ) ) ) );
       
        bindRuleSet ( d, "cnf_expandIfThenElse",
                      add ( not ( NotBelowQuantifierFeature.INSTANCE ),
                            onlyBelowQuanAndOr,
                            belowUnskolemisableQuantifier ) );

        
        final Feature pullOutQuantifierAllowed =
            add ( not ( NotBelowQuantifierFeature.INSTANCE ),
                  onlyBelowQuanAndOr,
                  applyTF ( FocusProjection.create ( 0 ),
                             sub ( ff.quantifiedClauseSet,
                                   ff.quantifiedClauseSet ) ) );        

        bindRuleSet ( d, "pullOutQuantifierUnifying", -20 );

        bindRuleSet ( d, "pullOutQuantifierAll",
                      add ( pullOutQuantifierAllowed,
                            ifZero ( FocusInAntecFeature.INSTANCE,
                                     longConst ( -20 ), longConst ( -40 ) ) ) );

        bindRuleSet ( d, "pullOutQuantifierEx",
                      add ( pullOutQuantifierAllowed,
                            ifZero ( FocusInAntecFeature.INSTANCE,
                                     longConst ( -40 ), longConst ( -20 ) ) ) );
    }

    private Feature clausesSmallerThan(String smaller, String bigger,
                                       IntegerLDT numbers) {
        return
        ClausesSmallerThanFeature.create ( instOf ( smaller ),
                                           instOf ( bigger ),
                                           numbers );
    }

    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Heuristic instantiation of quantified formulas
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private void setupQuantifierInstantiation(RuleSetDispatchFeature d) {
        if ( quantifierInstantiatedEnabled () ) {
            final TermBuffer varInst = new TermBuffer ();
            final Feature branchPrediction =
                InstantiationCostScalerFeature.create
                    ( InstantiationCost.create ( varInst ),
                      allowQuantifierSplitting () );
            
            bindRuleSet ( d, "gamma",
               SumFeature.createSum( new Feature[] {
                     FocusInAntecFeature.INSTANCE,
                     applyTF ( FocusProjection.create ( 0 ),
                               add ( ff.quantifiedClauseSet,
                                     instQuantifiersWithQueries () ?
                                          longTermConst ( 0 ) :
                                          ff.notContainsExecutable ) ),
                     forEach ( varInst, HeuristicInstantiation.INSTANCE,
                               add ( instantiate ( "t", varInst ),
                                     branchPrediction ) ) } ) );
        } else {
            bindRuleSet ( d, "gamma", inftyConst () );            
        }
    }

    private void setupQuantifierInstantiationApproval(RuleSetDispatchFeature d) {
        if ( quantifierInstantiatedEnabled () ) {
            final TermBuffer varInst = new TermBuffer ();
            
            bindRuleSet ( d, "gamma",
               add ( isInstantiated ( "t" ),
                     not ( sum ( varInst, HeuristicInstantiation.INSTANCE,
                                 not ( eq ( instOf ( "t" ), varInst ) ) ) ),
                     InstantiationCostScalerFeature.create
                             ( InstantiationCost.create ( instOf ( "t" ) ),
                               longConst ( 0 ) ) ) );
        } else {
            bindRuleSet ( d, "gamma", inftyConst () );            
        }
    }

    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Handling of arithmetic
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private static final int IN_EQ_SIMP_NON_LIN_COST = 1000;
    private static final int POLY_DIVISION_COST = -2250;
    
    private void setupArithPrimaryCategories(RuleSetDispatchFeature d) {
        // Gaussian elimination + Euclidian algorithm for linear equations;
        // Buchberger's algorithmus for handling polynomial equations over
        // the integers
            
        bindRuleSet ( d, "polySimp_expand", -4500 );
        bindRuleSet ( d, "polySimp_directEquations", -3000 );
        bindRuleSet ( d, "polySimp_pullOutGcd", -2250 );
        bindRuleSet ( d, "polySimp_leftNonUnit", -2000 );
        bindRuleSet ( d, "polySimp_saturate", 0 );

        // Omega test for handling linear arithmetic and inequalities over the
        // integers; cross-multiplication + case distinctions for nonlinear
        // inequalities
            
        bindRuleSet ( d, "inEqSimp_expand", -4500 );
        bindRuleSet ( d, "inEqSimp_directInEquations", -3000 );
        bindRuleSet ( d, "inEqSimp_propagation", -2500 );
        bindRuleSet ( d, "inEqSimp_pullOutGcd", -2250 );
        bindRuleSet ( d, "inEqSimp_saturate", -2000 );
        bindRuleSet ( d, "inEqSimp_forNormalisation", -1000 );
        bindRuleSet ( d, "inEqSimp_special_nonLin", -1400 );
        
        if ( arithNonLinInferences () )
            bindRuleSet ( d, "inEqSimp_nonLin", IN_EQ_SIMP_NON_LIN_COST );
        else
            bindRuleSet ( d, "inEqSimp_nonLin", inftyConst () );

        // polynomial division, simplification of fractions and mods
        bindRuleSet ( d, "polyDivision", POLY_DIVISION_COST );

    }

    private void setupPolySimp( RuleSetDispatchFeature d, IntegerLDT numbers) {
        
        // category "expansion" (normalising polynomial terms)
        
        bindRuleSet ( d, "polySimp_elimSubNeg", longConst ( -120 ) );

        bindRuleSet ( d, "polySimp_homo",
          add ( applyTF ( "homoRight",
                          add ( not ( tf.zeroLiteral ), tf.polynomial ) ),
                or ( applyTF ( "homoLeft", or ( tf.addF, tf.negMonomial ) ),
                     not ( monSmallerThan ( "homoRight", "homoLeft", numbers) ) ),
                longConst ( -120 ) ) );
        
        bindRuleSet ( d, "polySimp_pullOutFactor",
                      add ( applyTFNonStrict ( "pullOutLeft", tf.literal ),
                            applyTFNonStrict ( "pullOutRight", tf.literal ),
                            longConst ( -120 ) ) );

        bindRuleSet ( d, "polySimp_elimOneLeft", -120 );

        bindRuleSet ( d, "polySimp_elimOneRight", -120 );

        bindRuleSet ( d, "polySimp_mulOrder",
           add ( applyTF ( "commRight", tf.monomial ),
                 or ( applyTF ( "commLeft", tf.addF ),
       	              add ( applyTF ( "commLeft", tf.atom ),
                            atomSmallerThan ( "commLeft", "commRight", numbers ) ) ),
                 longConst ( -100 ) ) );

        bindRuleSet ( d, "polySimp_mulAssoc",
                      SumFeature.createSum( new Feature[] {
                            applyTF ( "mulAssocMono0", tf.monomial ),
                            applyTF ( "mulAssocMono1", tf.monomial ),
                            applyTF ( "mulAssocAtom", tf.atom ),
                            longConst ( -80 ) } ) );

        bindRuleSet ( d, "polySimp_addOrder",
           SumFeature.createSum( new Feature[] {
             applyTF ( "commLeft", tf.monomial ),
             applyTF ( "commRight", tf.polynomial ),
             monSmallerThan ( "commRight", "commLeft", numbers),
             longConst ( -60 ) } ) );

        
        bindRuleSet ( d, "polySimp_addAssoc",
                      SumFeature.createSum( new Feature[] {
                            applyTF ( "addAssocPoly0", tf.polynomial ),
                            applyTF ( "addAssocPoly1", tf.polynomial ),
                            applyTF ( "addAssocMono", tf.monomial ),
                            longConst ( -10 ) } ) );

        bindRuleSet ( d, "polySimp_dist",
                      SumFeature.createSum( new Feature[] {
                        applyTF ( "distSummand0", tf.polynomial ),
                        applyTF ( "distSummand1", tf.polynomial ),
                        ifZero ( applyTF ( "distCoeff", tf.monomial ),
                                 longConst ( -15 ),
                                 applyTF ( "distCoeff", tf.polynomial ) ),
                        applyTF ( "distSummand0", tf.polynomial ),
                        applyTF ( "distSummand1", tf.polynomial ),
                        longConst ( -35 ) } ) );

        // category "direct equations"
        
        bindRuleSet ( d, "polySimp_balance",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "sepResidue", tf.polynomial ),
             ifZero ( isInstantiated ( "sepPosMono" ),
               add ( applyTF ( "sepPosMono", tf.nonNegMonomial ),
                     monSmallerThan ( "sepResidue", "sepPosMono", numbers ) ) ),
             ifZero ( isInstantiated ( "sepNegMono" ),
               add ( applyTF ( "sepNegMono", tf.negMonomial ),
                     monSmallerThan ( "sepResidue", "sepNegMono", numbers ) ) ),
             longConst ( -30 )
           } ) );
        
        bindRuleSet ( d, "polySimp_normalise",
                      add ( applyTF ( "invertRight", tf.zeroLiteral ),
                            applyTF ( "invertLeft", tf.negMonomial ),
                            longConst ( -30 ) ) );
        
        // application of equations: some specialised rules that handle
        // monomials and their coefficients properly

        final TermBuffer eqLeft = new TermBuffer ();
        final TermBuffer focus = new TermBuffer ();

        final TermFeature atLeastTwoLCEquation =
            opSub ( Equality.EQUALS,
                    opSub ( tf.mul, tf.atom, tf.atLeastTwoLiteral ),
                    tf.intF );
        
        final Feature validEqApplication =
            add ( not ( eq ( eqLeft, focus ) ),
                  // otherwise, the normal equation rules can and should be used
                  ifZero ( applyTF ( AssumptionProjection.create ( 0 ),
                                     atLeastTwoLCEquation ),
                           add ( FocusInAntecFeature.INSTANCE,
                                 applyTF ( FocusFormulaProjection.INSTANCE,
                                           atLeastTwoLCEquation ) ) ),
                  ReducibleMonomialsFeature.createReducible ( focus, eqLeft ) );
        
        final Feature eq_monomial_feature =
            add ( not ( DirectlyBelowSymbolFeature.create ( tf.mul ) ),
                  ifZero ( MatchedIfFeature.INSTANCE,
                           let ( focus, FocusProjection.create ( 0 ),
                           let ( eqLeft,
                                 sub ( AssumptionProjection.create ( 0 ), 0 ), 
                                 validEqApplication ) ) ) );
        
        bindRuleSet ( d, "polySimp_applyEq",
                      add ( eq_monomial_feature, longConst ( 1 ) ) );

        bindRuleSet ( d, "polySimp_applyEqRigid",
                      add ( eq_monomial_feature, longConst ( 2 ) ) );

        // category "saturate"
        
        bindRuleSet ( d, "polySimp_critPair",
           ifZero ( MatchedIfFeature.INSTANCE,
                    add ( monSmallerThan ( "cpLeft1", "cpLeft2", numbers ),
                          not ( TrivialMonomialLCRFeature
                                .create ( instOf ( "cpLeft1" ),
                                          instOf ( "cpLeft2" ) ) ) ) ) );
    }
    

    // For taclets that need instantiation, but where the instantiation is
    // deterministic and does not have to be repeated at a later point, we
    // setup the same feature terms as in the instantiation method. The
    // definitions in <code>setupInstantiationWithoutRetry</code> should
    // give cost infinity to those incomplete rule applications that will
    // never be instantiated (so that these applications can be removed from
    // the queue and do not have to be considered again).
    private void setupPolySimpInstantiationWithoutRetry(RuleSetDispatchFeature d,
                                                        Proof p_proof) {
        final IntegerLDT numbers =
            p_proof.getServices().getTypeConverter().getIntegerLDT();

        
        // category "direct equations"

        setupPullOutGcd ( d, "polySimp_pullOutGcd", false );

        // category "polynomial division"

        setupDivModDivision ( d );

        // category "handling of equations with non-unit-coefficients on
        //           left-hand side"
        
        bindRuleSet ( d, "polySimp_newSym",
           ifZero ( not ( isInstantiated ( "newSymDef" ) ),
              SumFeature.createSum ( new Feature[] {
                applyTF ( "newSymLeft", tf.atom ),
                applyTF ( "newSymLeftCoeff", tf.atLeastTwoLiteral ),
                applyTF ( "newSymRight", tf.polynomial ),
                instantiate ( "newSymDef",
                              MonomialColumnOp
                              .create ( instOf ( "newSymLeftCoeff" ),
                                        instOf ( "newSymRight" ) ) ) } ) ) );
        
        final TermBuffer divisor = new TermBuffer ();
        final TermBuffer dividend = new TermBuffer ();

        bindRuleSet ( d, "polySimp_applyEqPseudo",
           add (
             applyTF ( "aePseudoTargetLeft", tf.monomial ),
             applyTF ( "aePseudoTargetRight", tf.polynomial ),
             ifZero (MatchedIfFeature.INSTANCE,
               SumFeature.createSum ( new Feature[] {
                  DiffFindAndIfFeature.INSTANCE,
                  applyTF ( "aePseudoLeft", add ( tf.nonCoeffMonomial,
                                                  not ( tf.atom ) ) ),
                  applyTF ( "aePseudoLeftCoeff", tf.atLeastTwoLiteral ),
                  applyTF ( "aePseudoRight", tf.polynomial ),
                  MonomialsSmallerThanFeature.create ( instOf ( "aePseudoRight" ),
                                                       instOf ( "aePseudoLeft" ),
                                                       numbers ),
                  let ( divisor, instOf ( "aePseudoLeft" ),
                  let ( dividend, instOf ( "aePseudoTargetLeft" ),
                  add ( ReducibleMonomialsFeature.createReducible ( dividend, divisor ),
                        instantiate ( "aePseudoTargetFactor",
                                      ReduceMonomialsProjection
                                      .create ( dividend, divisor ) ) ) ) ) } ) ) ) );
    }

    private void setupNewSymApproval(RuleSetDispatchFeature d, IntegerLDT numbers) {
        final TermBuffer antecFor = new TermBuffer ();
        final Feature columnOpEq =
            applyTF ( antecFor,
                      opSub ( tf.eq,
                              opSub ( tf.mul, tf.atom, tf.atLeastTwoLiteral ),
                              tf.polynomial ) );
        final Feature biggerLeftSide =
            MonomialsSmallerThanFeature
            .create ( instOf ( "newSymLeft" ),
                      subAt ( antecFor,
                              PosInTerm.TOP_LEVEL.down ( 0 ).down ( 0 ) ), numbers );
        bindRuleSet ( d, "polySimp_newSym",
           add ( isInstantiated ( "newSymDef" ),
                 sum ( antecFor, SequentFormulasGenerator.antecedent (),
                       not ( add ( columnOpEq, biggerLeftSide ) ) ) ) );
    }

    private Feature termSmallerThan(String smaller, String bigger) {
        return
        TermSmallerThanFeature.create ( instOf ( smaller ), instOf ( bigger ) );
    }

    private Feature monSmallerThan(String smaller, String bigger,
                                   IntegerLDT numbers) {
        return
        MonomialsSmallerThanFeature.create ( instOf ( smaller ), instOf ( bigger ),
                                             numbers );
    }

    private Feature atomSmallerThan(String smaller, String bigger,
                                    IntegerLDT numbers) {
        return
        AtomsSmallerThanFeature.create ( instOf ( smaller ), instOf ( bigger ),
                                         numbers );
    }

    private Feature literalsSmallerThan(String smaller, String bigger,
                                        IntegerLDT numbers) {
        return
        LiteralsSmallerThanFeature.create ( instOf ( smaller ), instOf ( bigger ),
                                            numbers );
    }

    
    private void setupPullOutGcd(RuleSetDispatchFeature d, String ruleSet,
                                 boolean roundingUp) {
        final TermBuffer gcd = new TermBuffer ();
        
        final Feature instantiateDivs;
        if ( roundingUp )
            instantiateDivs =
                add ( instantiate ( "elimGcdLeftDiv",
                                    DividePolynomialsProjection.createRoundingUp
                                    (gcd, instOf ( "elimGcdLeft" ) ) ),
                      instantiate ( "elimGcdRightDiv",
                                    DividePolynomialsProjection.createRoundingUp
                                    (gcd, instOf ( "elimGcdRight" ) ) ) );
        else
            instantiateDivs =
                add ( instantiate ( "elimGcdLeftDiv",
                                    DividePolynomialsProjection.createRoundingDown
                                    (gcd, instOf ( "elimGcdLeft" ) ) ),
                      instantiate ( "elimGcdRightDiv",
                                    DividePolynomialsProjection.createRoundingDown
                                    (gcd, instOf ( "elimGcdRight" ) ) ) );
        
        bindRuleSet ( d, ruleSet,
           add ( applyTF ( "elimGcdLeft", tf.nonNegMonomial ),
                 applyTF ( "elimGcdRight", tf.polynomial ),
                 let ( gcd,
                       CoeffGcdProjection.create ( instOf ( "elimGcdLeft" ),
                                                   instOf ( "elimGcdRight" ) ),
                       add ( applyTF ( gcd, tf.atLeastTwoLiteral ),
                             instantiate ( "elimGcd", gcd ),
                             instantiateDivs  ) ) ) );
    }    

    
    private void setupInEqSimp(RuleSetDispatchFeature d,
                               Proof p_proof,
                               IntegerLDT numbers) {
        
        // category "expansion" (normalising inequations)
 
        bindRuleSet ( d, "inEqSimp_moveLeft", -90 );

        bindRuleSet ( d, "inEqSimp_makeNonStrict", -80 );

        bindRuleSet ( d, "inEqSimp_commute",
                      SumFeature.createSum ( new Feature[] {
                        applyTF ( "commRight", tf.monomial ),
                        applyTF ( "commLeft", tf.polynomial ),
                        monSmallerThan ( "commLeft", "commRight", numbers ),
                        longConst ( -40 ) } ) );

        // this is copied from "polySimp_homo"
        bindRuleSet ( d, "inEqSimp_homo",
           add ( applyTF ( "homoRight",
                             add ( not ( tf.zeroLiteral ), tf.polynomial ) ),
                 or ( applyTF ( "homoLeft", or ( tf.addF, tf.negMonomial ) ),
                      not ( monSmallerThan ( "homoRight", "homoLeft", numbers) ) ) ) );

        // category "direct inequations"

        // this is copied from "polySimp_balance"
        bindRuleSet ( d, "inEqSimp_balance",
           add (
             applyTF ( "sepResidue", tf.polynomial ),
             ifZero ( isInstantiated ( "sepPosMono" ),
                add ( applyTF ( "sepPosMono", tf.nonNegMonomial ),
                      monSmallerThan ( "sepResidue", "sepPosMono", numbers ) ) ),
             ifZero ( isInstantiated ( "sepNegMono" ),
                add ( applyTF ( "sepNegMono", tf.negMonomial ),
                      monSmallerThan ( "sepResidue", "sepNegMono", numbers ) ) )
             ) );
        
        // this is copied from "polySimp_normalise"
        bindRuleSet ( d, "inEqSimp_normalise",
                      add ( applyTF ( "invertRight", tf.zeroLiteral ),
                            applyTF ( "invertLeft", tf.negMonomial ) ) );

        // category "saturate"
        
        bindRuleSet ( d, "inEqSimp_antiSymm", longConst ( -20 ) );

        bindRuleSet ( d, "inEqSimp_exactShadow",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "esLeft", tf.nonCoeffMonomial ),
             applyTFNonStrict ( "esCoeff2", tf.nonNegLiteral ),
             applyTF ( "esRight2", tf.polynomial ),
             ifZero ( MatchedIfFeature.INSTANCE,
                    SumFeature.createSum ( new Feature[] {
                      applyTFNonStrict ( "esCoeff1", tf.nonNegLiteral ),
                      applyTF ( "esRight1", tf.polynomial ),
                      not ( PolynomialValuesCmpFeature
                            .leq ( instOf ( "esRight2" ),
                                   instOf ( "esRight1" ),
                                   instOfNonStrict ( "esCoeff1" ),
                                   instOfNonStrict ( "esCoeff2" ) ))
                    } ) ) } ) );

        // category "propagation"

        bindRuleSet ( d, "inEqSimp_contradInEqs",
           add ( applyTF ( "contradLeft", tf.monomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum ( new Feature[] {
                     DiffFindAndIfFeature.INSTANCE,
                     applyTF ( "contradRightSmaller", tf.polynomial ),
                     applyTF ( "contradRightBigger", tf.polynomial ),
                     applyTFNonStrict ( "contradCoeffSmaller", tf.posLiteral ),
                     applyTFNonStrict ( "contradCoeffBigger", tf.posLiteral ),
                     PolynomialValuesCmpFeature
                     .lt ( instOf ( "contradRightSmaller" ),
                           instOf ( "contradRightBigger" ),
                           instOfNonStrict ( "contradCoeffBigger" ),
                           instOfNonStrict ( "contradCoeffSmaller" ) ) } ) ) ) );

        bindRuleSet ( d, "inEqSimp_contradEqs",
           add ( applyTF ( "contradLeft", tf.monomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum ( new Feature[] {
                     applyTF ( "contradRightSmaller", tf.polynomial ),
                     applyTF ( "contradRightBigger", tf.polynomial ),
                     PolynomialValuesCmpFeature
                     .lt ( instOf ( "contradRightSmaller" ),
                           instOf ( "contradRightBigger" ) ) } ) ),
                 longConst ( -60 ) ) );

        bindRuleSet ( d, "inEqSimp_strengthen", longConst ( -30 ) );

        bindRuleSet ( d, "inEqSimp_subsumption",
           add ( applyTF ( "subsumLeft", tf.monomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum ( new Feature[] {
                     DiffFindAndIfFeature.INSTANCE,
                     applyTF ( "subsumRightSmaller", tf.polynomial ),
                     applyTF ( "subsumRightBigger", tf.polynomial ),
                     applyTFNonStrict ( "subsumCoeffSmaller", tf.posLiteral ),
                     applyTFNonStrict ( "subsumCoeffBigger", tf.posLiteral ),
                     PolynomialValuesCmpFeature
                     .leq ( instOf ( "subsumRightSmaller" ),
                            instOf ( "subsumRightBigger" ),
                            instOfNonStrict ( "subsumCoeffBigger" ),
                            instOfNonStrict ( "subsumCoeffSmaller" ) ) } ) ) ) );

        // category "handling of non-linear inequations"
        
        if ( arithNonLinInferences () ) {
            setupMultiplyInequations ( d, longConst ( 100 ) );
         
            bindRuleSet ( d, "inEqSimp_split_eq",
                          add ( TopLevelFindFeature.SUCC, longConst ( -100 ) ) );

            bindRuleSet ( d, "inEqSimp_signCases",
                          not ( isInstantiated ( "signCasesLeft" ) ) );
        }
        
        // category "normalisation of formulas"
        // (e.g., quantified formulas, where the normal sequent calculus
        // does not do any normalisation)
        
        bindRuleSet ( d, "inEqSimp_and_contradInEqs",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "contradLeft", tf.monomial ),
             applyTF ( "contradRightSmaller", tf.polynomial ),
             applyTF ( "contradRightBigger", tf.polynomial ),
             PolynomialValuesCmpFeature
             .lt ( instOf ( "contradRightSmaller" ),
                   instOf ( "contradRightBigger" ) ) } ) );

        bindRuleSet ( d, "inEqSimp_andOr_subsumption",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "subsumLeft", tf.monomial ),
             applyTF ( "subsumRightSmaller", tf.polynomial ),
             applyTF ( "subsumRightBigger", tf.polynomial ),
             PolynomialValuesCmpFeature
             .leq ( instOf ( "subsumRightSmaller" ),
                    instOf ( "subsumRightBigger" ) ) } ) );
        
        bindRuleSet ( d, "inEqSimp_and_subsumptionEq",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "subsumLeft", tf.monomial ),
             applyTF ( "subsumRightSmaller", tf.polynomial ),
             applyTF ( "subsumRightBigger", tf.polynomial ),
             PolynomialValuesCmpFeature
             .lt ( instOf ( "subsumRightSmaller" ),
                    instOf ( "subsumRightBigger" ) ) } ) );
                   
        final TermBuffer one = new TermBuffer ();
        one.setContent ( TermBuilder.DF.zTerm ( p_proof.getServices (), "1" ) );
        final TermBuffer two = new TermBuffer ();
        two.setContent ( TermBuilder.DF.zTerm ( p_proof.getServices (), "2" ) );

        bindRuleSet ( d, "inEqSimp_or_tautInEqs",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "tautLeft", tf.monomial ),
             applyTF ( "tautRightSmaller", tf.polynomial ),
             applyTF ( "tautRightBigger", tf.polynomial ),
             PolynomialValuesCmpFeature
             .leq ( instOf ( "tautRightSmaller" ),
                    opTerm ( numbers.getAdd(),
                             one, instOf ( "tautRightBigger" ) ) ) } ) );

        bindRuleSet ( d, "inEqSimp_or_weaken",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "weakenLeft", tf.monomial ),
             applyTF ( "weakenRightSmaller", tf.polynomial ),
             applyTF ( "weakenRightBigger", tf.polynomial ),
             PolynomialValuesCmpFeature
             .eq ( opTerm ( numbers.getAdd (),
                            one, instOf ( "weakenRightSmaller" ) ),
                   instOf ( "weakenRightBigger" ) ) } ) );

        bindRuleSet ( d, "inEqSimp_or_antiSymm",
           SumFeature.createSum ( new Feature[] {
             applyTF ( "antiSymmLeft", tf.monomial ),
             applyTF ( "antiSymmRightSmaller", tf.polynomial ),
             applyTF ( "antiSymmRightBigger", tf.polynomial ),
             PolynomialValuesCmpFeature
             .eq ( opTerm ( numbers.getAdd (),
                            two, instOf ( "antiSymmRightSmaller" ) ),
                   instOf ( "antiSymmRightBigger" ) ) } ) );

    }

    private void setupMultiplyInequations(RuleSetDispatchFeature d,
                                          Feature notAllowedF) {
        final TermBuffer intRel = new TermBuffer ();
        
/*        final Feature partiallyBounded =
            not ( sum ( intRel, SequentFormulasGenerator.sequent (),
                        not ( add ( applyTF ( intRel, tf.intRelation ),
                                    InEquationMultFeature
                                    .partiallyBounded ( instOf ( "multLeft" ),
                                                        instOf ( "multFacLeft" ),
                                                        sub ( intRel, 0 ) ) ) ) ) ); */
        
        final Feature totallyBounded =
            not ( sum ( intRel, SequentFormulasGenerator.sequent (),
                        not ( add ( applyTF ( intRel, tf.intRelation ),
                                    InEquationMultFeature
                                    .totallyBounded ( instOf ( "multLeft" ),
                                                      instOf ( "multFacLeft" ),
                                                      sub ( intRel, 0 ) ) ) ) ) );
        
        final Feature exactlyBounded =
            not ( sum ( intRel, SequentFormulasGenerator.sequent (),
                        not ( add ( applyTF ( intRel, tf.intRelation ),
                                    InEquationMultFeature
                                    .exactlyBounded ( instOf ( "multLeft" ),
                                                      instOf ( "multFacLeft" ),
                                                      sub ( intRel, 0 ) ) ) ) ) );
        
        // this is a bit hackish
        //
        // really, one would need a possibility to express that the cost
        // computation for the rule application should be post-poned (and
        // repeated at a later point) if the product of the left sides does not
        // have any similarity with existing left sides
        // (<code>AllowInEquationMultiplication</code> returns false). We
        // simulate this by returning non-infinite costs here, but by declining
        // the rule application in <code>isApprovedApp</code>). This is not
        // perfect, because it is not possible to distinguish between the
        // re-cost-computation delay and the normal costs for a rule application
        bindRuleSet ( d, "inEqSimp_nonLin_multiply",
           add ( applyTF ( "multLeft", tf.nonNegMonomial ),
                 applyTF ( "multRight", tf.polynomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum ( new Feature[] {
                     applyTF ( "multFacLeft", tf.nonNegMonomial ),
                     ifZero ( applyTF ( "multRight", tf.literal ),
                              longConst ( -100 ) ),
                     ifZero ( applyTF ( "multFacRight", tf.literal ),
                              longConst ( -100 ),
                              applyTF ( "multFacRight", tf.polynomial ) ),
/*                ifZero ( applyTF ( "multRight", tf.literal ),
                         longConst ( -100 ),
                         applyTF ( "multRight", tf.polynomial ) ),
                ifZero ( applyTF ( "multFacRight", tf.literal ),
                         longConst ( -100 ),
                         applyTF ( "multFacRight", tf.polynomial ) ), */
                     not ( TermSmallerThanFeature.create
			   ( FocusProjection.create ( 0 ),
			     AssumptionProjection.create ( 0 ) ) ),
                     ifZero ( exactlyBounded,
                              longConst ( 0 ),
                              ifZero ( totallyBounded,
                                       longConst ( 100 ),
                                       notAllowedF ) ),
/*                                       ifZero ( partiallyBounded,
                                                longConst ( 400 ),
                                                notAllowedF ) ) ), */
/*                     applyTF ( "multLeft", rec ( tf.mulF, longTermConst ( 20 ) ) ),
                     applyTF ( "multFacLeft", rec ( tf.mulF, longTermConst ( 20 ) ) ),
                     applyTF ( "multRight", rec ( tf.addF, longTermConst ( 4 ) ) ),
                     applyTF ( "multFacRight", rec ( tf.addF, longTermConst ( 4 ) ) ), */
                   } ),
                   notAllowedF ) ) );
    }
    
    private void setupInEqSimpInstantiation(RuleSetDispatchFeature d,
                                            Proof p_proof) {
        // category "handling of non-linear inequations"

        setupSquaresAreNonNegative ( d );
        
        if ( arithNonLinInferences() )            
            setupInEqCaseDistinctions ( d, p_proof );
    }

    // For taclets that need instantiation, but where the instantiation is
    // deterministic and does not have to be repeated at a later point, we
    // setup the same feature terms as in the instantiation method. The
    // definitions in <code>setupInstantiationWithoutRetry</code> should
    // give cost infinity to those incomplete rule applications that will
    // never be instantiated (so that these applications can be removed from
    // the queue and do not have to be considered again).
    private void setupInEqSimpInstantiationWithoutRetry(RuleSetDispatchFeature d,
                                                        Proof p_proof) {
        // category "direct inequations"

        setupPullOutGcd ( d, "inEqSimp_pullOutGcd_leq", false );
        setupPullOutGcd ( d, "inEqSimp_pullOutGcd_geq", true );
        
        // more efficient (but not confluent) versions for the antecedent
        bindRuleSet ( d, "inEqSimp_pullOutGcd_antec", -10 );
        
        // category "handling of non-linear inequations"
        
        final TermBuffer divisor = new TermBuffer ();
        final TermBuffer dividend = new TermBuffer ();
            
        bindRuleSet ( d, "inEqSimp_nonLin_divide",
          SumFeature.createSum ( new Feature[] {
            applyTF ( "divProd", tf.nonCoeffMonomial ),
            applyTFNonStrict ( "divProdBoundNonPos", tf.nonPosLiteral ),
            applyTFNonStrict ( "divProdBoundNonNeg", tf.nonNegLiteral ),
            ifZero ( MatchedIfFeature.INSTANCE,
              let ( divisor, instOf ( "divX" ),
              let ( dividend, instOf ( "divProd" ),
              SumFeature.createSum ( new Feature[] {
                applyTF ( divisor, tf.nonCoeffMonomial ),
                not ( eq ( dividend, divisor ) ),
                applyTFNonStrict ( "divXBoundPos", tf.posLiteral ),
                applyTFNonStrict ( "divXBoundNeg", tf.negLiteral ),
                ReducibleMonomialsFeature.createReducible ( dividend, divisor ),
                instantiate ( "divY", ReduceMonomialsProjection
                                      .create ( dividend, divisor ) )
              } ) ) ) )
          } ) );

        setupNonLinTermIsPosNeg ( d, "inEqSimp_nonLin_pos", true );
        setupNonLinTermIsPosNeg ( d, "inEqSimp_nonLin_neg", false );
    }

    private void setupNonLinTermIsPosNeg(RuleSetDispatchFeature d,
                                         String ruleSet,
                                         boolean pos) {
        final TermBuffer divisor = new TermBuffer ();
        final TermBuffer dividend = new TermBuffer ();
        final TermBuffer quotient = new TermBuffer ();
        final TermBuffer antecFor = new TermBuffer ();

        bindRuleSet ( d, ruleSet,
          SumFeature.createSum ( new Feature[] {
            applyTF ( "divProd", tf.nonCoeffMonomial ),
            applyTFNonStrict ( "divProdBoundPos", tf.posLiteral ),
            applyTFNonStrict ( "divProdBoundNeg", tf.negLiteral ),
            ifZero ( MatchedIfFeature.INSTANCE,
              let ( divisor, instOf ( "divX" ),
              let ( dividend, instOf ( "divProd" ),
              SumFeature.createSum ( new Feature[] {
                applyTF ( divisor, tf.nonCoeffMonomial ),
                not ( applyTF ( dividend, eq ( divisor ) ) ),
                applyTFNonStrict ( "divXBoundNonPos", tf.nonPosLiteral ),
                applyTFNonStrict ( "divXBoundNonNeg", tf.nonNegLiteral ),
                ReducibleMonomialsFeature.createReducible ( dividend, divisor ),
                let ( quotient,
                      ReduceMonomialsProjection.create ( dividend, divisor ),
                      add ( sum ( antecFor,
                                  SequentFormulasGenerator.antecedent (),
                                  not ( applyTF ( antecFor,
                                                  pos ?
                                                  opSub ( tf.geq,
                                                          eq ( quotient ),
                                                          tf.posLiteral )
                                                  :
                                                  opSub ( tf.leq,
                                                          eq ( quotient ),
                                                          tf.negLiteral ) ) ) ),
                            instantiate ( "divY", quotient ) ) )
              } ) ) ) )
          } ) );
    }

    private void setupSquaresAreNonNegative(RuleSetDispatchFeature d) {
        final TermBuffer intRel  = new TermBuffer ();
        final TermBuffer product = new TermBuffer ();
        final TermBuffer factor  = new TermBuffer ();

        final Feature productContainsSquare =
            applyTF ( sub ( product, 0 ),
                      or ( eq ( factor ),
                           opSub ( tf.mul, any (), eq ( factor ) ) ) );
        final Feature productIsProduct =
            applyTF ( product, opSub ( tf.mul, any (), not ( tf.mulF ) ) );
        
        bindRuleSet ( d, "inEqSimp_nonNegSquares",
          forEach ( intRel, SequentFormulasGenerator.sequent (),
             ifZero ( applyTF ( intRel, tf.intRelation ),
                forEach ( product,
                          SubtermGenerator.leftTraverse ( sub ( intRel, 0 ), tf.mulF ),
                   ifZero ( productIsProduct,
                            let ( factor, sub ( product, 1 ),
                                  ifZero ( productContainsSquare,
                                           instantiate ( "squareFac", factor ) ) )
                            ) ) ) ) );
    }


    private void setupInEqCaseDistinctions(RuleSetDispatchFeature d,
                                           Proof p_proof) {
        final TermBuffer intRel = new TermBuffer ();
        final TermBuffer atom = new TermBuffer ();
        final TermBuffer zero = new TermBuffer ();
        zero.setContent ( TermBuilder.DF.zTerm ( p_proof.getServices (), "0" ) );
        final TermBuffer rootInf = new TermBuffer ();

        final Feature posNegSplitting =
           forEach ( intRel, SequentFormulasGenerator.antecedent (),
             add ( applyTF ( intRel, tf.intRelation ),
                   forEach ( atom,
                             SubtermGenerator.leftTraverse ( sub ( intRel, 0 ), tf.mulF ),
                      SumFeature.createSum ( new Feature[] {
                        applyTF ( atom, add ( tf.atom, not ( tf.literal ) ) ),
                        allowPosNegCaseDistinction ( atom ),
                        instantiate ( "signCasesLeft", atom ),
                        longConst ( IN_EQ_SIMP_NON_LIN_COST + 200 )
//			            ,
//                      applyTF ( atom, rec ( any (), longTermConst ( 5 ) ) )
                      } ) ) ) );
        
        bindRuleSet ( d, "inEqSimp_signCases", posNegSplitting ); 

        final Feature strengthening =
            forEach ( intRel, SequentFormulasGenerator.antecedent (),
              SumFeature.createSum ( new Feature[] {
                    applyTF ( intRel, add ( or ( tf.geqF, tf.leqF ),
                                            sub ( tf.atom, tf.literal ) ) ),
                    instantiate ( "cutFormula",
                                  opTerm ( tf.eq,
                                           sub ( intRel, 0 ), sub ( intRel, 1 ) ) ),
                    longConst ( IN_EQ_SIMP_NON_LIN_COST + 300 )
//		            ,
//                  applyTF ( sub ( intRel, 0 ),
//                            rec ( any (), longTermConst ( 5 ) ) )
              } ) );
        
        final Feature rootInferences =
            forEach ( intRel, SequentFormulasGenerator.antecedent (),
              add ( isRootInferenceProducer ( intRel ),
                    forEach ( rootInf, RootsGenerator.create ( intRel ),
                              add ( instantiate ( "cutFormula", rootInf ),
                                    ifZero ( applyTF ( rootInf, op ( Junctor.OR ) ),
                                             longConst ( 50 ) ),
                                    ifZero ( applyTF ( rootInf, op ( Junctor.AND ) ),
                                             longConst ( 20 ) ) ) ),
                    longConst ( IN_EQ_SIMP_NON_LIN_COST )
              ) );
        
        bindRuleSet ( d, "cut", oneOf ( new Feature[] { strengthening,
                                                        rootInferences } ) );
    }

    private Feature isRootInferenceProducer(TermBuffer intRel) {
        return applyTF ( intRel, add ( tf.intRelation,
                                        sub ( tf.nonCoeffMonomial,
                                              tf.literal ) ) );
    }

    private Feature allowPosNegCaseDistinction(TermBuffer atom) {
        final TermBuffer antecFor = new TermBuffer ();
        final TermFeature eqAtom = eq ( atom );
        
        return
         add ( not ( succIntEquationExists () ),
               sum ( antecFor, SequentFormulasGenerator.antecedent (),
                     not ( applyTF ( antecFor,
                            or ( opSub ( tf.eq, eqAtom, any () ),
                                 opSub ( tf.leq, eqAtom, tf.negLiteral ),
                                 opSub ( tf.geq, eqAtom, tf.posLiteral ) ) ) ) ) );
    }

    private Feature allowInEqStrengthening(TermBuffer atom, TermBuffer literal) {
        final TermBuffer antecFor = new TermBuffer ();

        return
         add ( not ( succIntEquationExists () ),
               not ( sum ( antecFor, SequentFormulasGenerator.antecedent (),
                           not ( applyTF ( antecFor,
                                           add ( or ( tf.leqF, tf.geqF ),
                                                 sub ( eq ( atom ),
                                                       eq ( literal ) ) ) ) ) ) ) );
    }

    private Feature succIntEquationExists() {
        final TermBuffer succFor = new TermBuffer ();

        return not ( sum ( succFor, SequentFormulasGenerator.succedent (),
                           not ( applyTF ( succFor, tf.intEquation ) ) ) );
    }
    
    private void setupInEqCaseDistinctionsApproval(RuleSetDispatchFeature d) {
        final TermBuffer atom = new TermBuffer ();
        final TermBuffer literal = new TermBuffer ();
        final TermBuffer intRel = new TermBuffer ();
        final TermBuffer rootInf = new TermBuffer ();
        
        bindRuleSet ( d, "inEqSimp_signCases",
                      add ( isInstantiated("signCasesLeft" ),
                          let ( atom, instOf ( "signCasesLeft" ),
                                allowPosNegCaseDistinction ( atom ) ) ) );
        
        // this is somewhat ugly. we should introduce some concept of "tagging"
        // rule application so that they can be recognised again later
        bindRuleSet ( d, "cut",
           add ( isInstantiated ( "cutFormula" ),
            or ( not ( sum ( intRel, SequentFormulasGenerator.antecedent (),
                             ifZero ( isRootInferenceProducer ( intRel ),
                                      sum ( rootInf,
                                            RootsGenerator.create ( intRel ),
                                            not ( eq ( instOf ( "cutFormula" ),
                                                       rootInf ) ) ) ) ) ),
                 ifZero ( applyTF ( "cutFormula",
                                    opSub ( tf.eq, tf.atom, tf.literal ) ),
                          let ( atom, sub ( instOf ( "cutFormula" ), 0 ),
                          let ( literal, sub ( instOf ( "cutFormula" ), 1 ),
                                allowInEqStrengthening ( atom, literal ) ) ) ) ) ) );
    }

    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Axiomatisation and algorithms for further arithmetic operations:
    // division, modulus, modular Java operations
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private void setupDefOpsPrimaryCategories(RuleSetDispatchFeature d) {
        
        if ( arithDefOps () ) {
        // the axiom defining division only has to be inserted once, because
        // it adds equations to the antecedent
            bindRuleSet ( d, "defOps_div",
               SumFeature.createSum ( new Feature[] {
                 NonDuplicateAppModPositionFeature.INSTANCE,
                 applyTF ( "divNum", tf.polynomial ),
                 applyTF ( "divDenom", tf.polynomial ),
                 applyTF ( "divNum", tf.notContainsDivMod ),
                 applyTF ( "divDenom", tf.notContainsDivMod ),
                 ifZero ( isBelow ( ff.modalOperator ),
                          longConst ( 200 ) ) } ) );
        
            bindRuleSet ( d, "defOps_jdiv",
               SumFeature.createSum ( new Feature[] {
                 NonDuplicateAppModPositionFeature.INSTANCE,
                 applyTF ( "divNum", tf.polynomial ),
                 applyTF ( "divDenom", tf.polynomial ),
                 applyTF ( "divNum", tf.notContainsDivMod ),
                 applyTF ( "divDenom", tf.notContainsDivMod ),
                 ifZero ( isBelow ( ff.modalOperator ),
                          longConst ( 200 ) ) } ) );
        
            bindRuleSet ( d, "defOps_jdiv_inline",
                          add ( applyTF ( "divNum", tf.literal ),
                                applyTF ( "divDenom", tf.polynomial ),
                                longConst ( -5000 ) ) );
                   
            setupDefOpsExpandMod ( d );
            
            bindRuleSet ( d, "defOps_expandRanges", -5000 );
            bindRuleSet ( d, "defOps_expandJNumericOp", -500 );
            bindRuleSet ( d, "defOps_modHomoEq", -5000 );
        } else {
            bindRuleSet ( d, "defOps_div", inftyConst () );
            bindRuleSet ( d, "defOps_jdiv", inftyConst () );
            
            bindRuleSet ( d, "defOps_jdiv_inline",
                          add ( applyTF ( "divNum", tf.literal ),
                                applyTF ( "divDenom", tf.literal ),
                                longConst ( -4000 ) ) );

            bindRuleSet ( d, "defOps_mod",
                          add ( applyTF ( "divNum", tf.literal ),
                                applyTF ( "divDenom", tf.literal ),
                                longConst ( -4000 ) ) );

            bindRuleSet ( d, "defOps_expandRanges", inftyConst () );
            bindRuleSet ( d, "defOps_expandJNumericOp", inftyConst () );
            bindRuleSet ( d, "defOps_modHomoEq", inftyConst () );
        }
        
    }

    private void setupDefOpsExpandMod(RuleSetDispatchFeature d) {
        final TermBuffer superTerm = new TermBuffer ();
        
        final Feature subsumedModulus =
            add ( applyTF ( superTerm,
                            sub ( opSub ( tf.mod, any (), tf.literal ),
                                  tf.zeroLiteral ) ),
                  PolynomialValuesCmpFeature
                  .divides ( instOf ( "divDenom" ),
                             sub ( sub ( superTerm, 0 ), 1 ) ) );
        
        final Feature exSubsumedModulus =
            add ( applyTF ( "divDenom", tf.literal ),
                  not ( sum ( superTerm,
                              SuperTermGenerator.upwardsWithIndex
                                   ( sub ( or ( tf.addF, tf.mulF ), any () ) ),
                              not ( subsumedModulus ) ) ) );
        
        bindRuleSet ( d, "defOps_mod",
           ifZero ( add ( applyTF ( "divNum", tf.literal ),
                          applyTF ( "divDenom", tf.literal ) ),
                    longConst ( -4000 ),
                    SumFeature.createSum ( new Feature[] {
                       applyTF ( "divNum", tf.polynomial ),
                       applyTF ( "divDenom", tf.polynomial ),
		       ifZero ( isBelow ( ff.modalOperator ),
				exSubsumedModulus,
				or ( add ( applyTF ( "divNum",
						     tf.notContainsDivMod ),
					   applyTF ( "divDenom",
						     tf.notContainsDivMod ) ),
				     exSubsumedModulus ) ),
		       longConst ( -3500 )
                    } ) ) );
    }

    private Feature isBelow(TermFeature t) {
        final TermBuffer superTerm = new TermBuffer ();
        return not ( sum ( superTerm,
                           SuperTermGenerator.upwards ( any () ),
                           not ( applyTF ( superTerm, t ) ) ) );
    }

    private void setupDivModDivision(RuleSetDispatchFeature d) {
        
        final TermBuffer denomLC = new TermBuffer ();
        final TermBuffer numTerm = new TermBuffer ();
        final TermBuffer divCoeff = new TermBuffer ();
        
        // exact polynomial division
        
        final Feature checkNumTerm =
            ifZero ( add ( not ( applyTF ( numTerm, tf.addF ) ),
                           ReducibleMonomialsFeature
                                       .createReducible ( numTerm, denomLC ) ),
                     add ( instantiate ( "polyDivCoeff",
                                         ReduceMonomialsProjection
                                                .create ( numTerm, denomLC )),
                           inftyConst () ) );

        final Feature isReduciblePoly =
            sum ( numTerm,
                  SubtermGenerator.rightTraverse ( instOf ( "divNum" ), tf.addF ),
                  checkNumTerm );
        
        // polynomial division modulo equations of the antecedent
        
        final Feature checkCoeffE =
            ifZero ( contains ( divCoeff, FocusProjection.create ( 0 ) ),
                     // do not apply if the result contains the original term
                     longConst ( 0 ),
                     add ( instantiate ( "polyDivCoeff", divCoeff ),
                           inftyConst () ) );

        final Feature isReduciblePolyE =
            sum ( numTerm,
                  SubtermGenerator.rightTraverse ( instOf ( "divNum" ), tf.addF ),
                  ifZero ( applyTF ( numTerm, tf.addF ),
                           longConst ( 0 ),
                           sum ( divCoeff,
                                 MultiplesModEquationsGenerator
                                                .create ( numTerm, denomLC ),
                                 checkCoeffE ) ) );
        
        bindRuleSet ( d, "defOps_divModPullOut",
           SumFeature.createSum ( new Feature[] {
             not ( add ( applyTF ( "divNum", tf.literal ),
                         applyTF ( "divDenom", tf.literal ) ) ),
             applyTF ( "divNum", tf.polynomial ),
             applyTF ( "divDenom", tf.polynomial ),
             ifZero ( applyTF ( "divDenom", tf.addF ),
                let ( denomLC, sub ( instOf ( "divDenom" ), 1 ),
                      not ( isReduciblePoly ) ),
                let ( denomLC, instOf ( "divDenom" ),
                      ifZero ( isReduciblePoly,
                               // no possible division has been found so far
                               add ( NotInScopeOfModalityFeature.INSTANCE,
                                     ifZero ( isReduciblePolyE,
                                              // try again later
                                              longConst ( -POLY_DIVISION_COST )
                      ) ) ) ) ),
             longConst ( 100 ) } ) );
        
    }
    

    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the approval of complete taclet applications
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private Feature setupApprovalF(Proof p_proof) {
        return add ( NonDuplicateAppFeature.INSTANCE,
                     UCIncompatibleFeature.create ( p_proof ) );
    }
    
    private RuleSetDispatchFeature setupApprovalDispatcher(Proof p_proof) {
        final RuleSetDispatchFeature d = RuleSetDispatchFeature.create ();

        final IntegerLDT numbers =
            p_proof.getServices().getTypeConverter().getIntegerLDT();

        if ( arithNonLinInferences () )
            setupMultiplyInequations ( d, inftyConst () );

        // these taclets are not supposed to be applied with metavariable
        // instantiations
        bindRuleSet ( d, "inEqSimp_pullOutGcd", isInstantiated ( "elimGcd" ) );
        bindRuleSet ( d, "polySimp_pullOutGcd", isInstantiated ( "elimGcd" ) );

        bindRuleSet ( d, "inEqSimp_nonNegSquares", isInstantiated ( "squareFac" ) );
        bindRuleSet ( d, "inEqSimp_nonLin_divide", isInstantiated ( "divY" ) );
        bindRuleSet ( d, "inEqSimp_nonLin_pos", isInstantiated ( "divY" ) );
        bindRuleSet ( d, "inEqSimp_nonLin_neg", isInstantiated ( "divY" ) );

        bindRuleSet ( d, "inEqSimp_signCases", isInstantiated ( "signCasesLeft" ) );

        setupNewSymApproval ( d, numbers );

        bindRuleSet ( d, "defOps_div", NonDuplicateAppModPositionFeature.INSTANCE );
        bindRuleSet ( d, "defOps_jdiv", NonDuplicateAppModPositionFeature.INSTANCE );

        if ( arithNonLinInferences () )
            setupInEqCaseDistinctionsApproval ( d );
        
        bindRuleSet ( d, "inReachableStateImplication",
                      NonDuplicateAppModPositionFeature.INSTANCE );

        setupQuantifierInstantiationApproval ( d );
        setupSplittingApproval ( d );

        return d;
    }
    
    
    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the instantiation of incomplete taclet
    // applications
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////


    private RuleSetDispatchFeature setupInstantiationF(Proof p_proof) {
        enableInstantiate ();
        
        final RuleSetDispatchFeature d = RuleSetDispatchFeature.create ();
        
        setupQuantifierInstantiation ( d );
        
        setupArithPrimaryCategories ( d );
        setupDefOpsPrimaryCategories ( d );
        
        setupInstantiationWithoutRetry ( d, p_proof );

        setupInEqSimpInstantiation ( d, p_proof );
        
        disableInstantiate ();
        return d;
    }


    /**
     * For taclets that need instantiation, but where the instantiation is
     * deterministic and does not have to be repeated at a later point, we setup
     * the same feature terms both in the cost computation method and in the
     * instantiation method. The definitions in
     * <code>setupInstantiationWithoutRetry</code> should give cost infinity
     * to those incomplete rule applications that will never be instantiated (so
     * that these applications can be removed from the queue and do not have to
     * be considered again).
     */
    private void setupInstantiationWithoutRetry(RuleSetDispatchFeature d,
                                                Proof p_proof) {
        setupPolySimpInstantiationWithoutRetry ( d, p_proof );
        setupInEqSimpInstantiationWithoutRetry ( d, p_proof );
    }

    
    public Name name () {
        return new Name("JavaCardDLStrategy");
    }


    /**
	 * Evaluate the cost of a <code>RuleApp</code>.
	 * 
	 * @return the cost of the rule application expressed as a
	 *         <code>RuleAppCost</code> object.
	 *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule
	 *         shall not be applied at all (it is discarded by the strategy).
	 */
    public final RuleAppCost computeCost (RuleApp app,
                                          PosInOccurrence pio,
                                          Goal goal) {
        return costComputationF.compute ( app, pio, goal );
    }

    /**
	 * Re-Evaluate a <code>RuleApp</code>. This method is called immediately
	 * before a rule is really applied
	 * 
	 * @return true iff the rule should be applied, false otherwise
	 */
    public final boolean isApprovedApp (RuleApp app,
                                        PosInOccurrence pio,
                                        Goal goal) {
        return !( approvalF.compute ( app, pio, goal ) instanceof TopRuleAppCost );
    }
    
    protected final RuleAppCost instantiateApp(RuleApp app,
                                               PosInOccurrence pio,
                                               Goal goal) {
        return instantiationF.compute ( app, pio, goal );
    }
    

    public static class Factory extends StrategyFactory {
        public Factory () {
        }

        public Strategy create ( Proof p_proof, 
                StrategyProperties strategyProperties) {     
            return new JavaCardDLStrategy ( p_proof, strategyProperties );
        }
        
        public Name name () {
            return new Name("JavaCardDLStrategy");
        }
    }

    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Termfeatures: characterisations of terms and formulas
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    private final ArithTermFeatures tf;
    private final FormulaTermFeatures ff;
    
    private class ArithTermFeatures {

        public ArithTermFeatures (IntegerLDT numbers){
            Z = numbers.getNumberSymbol ();

            add = numbers.getAdd();
            mul = numbers.getMul();
            mod = numbers.getMod();
            div = numbers.getDiv ();
            jmod = numbers.getJModulo ();
            jdiv = numbers.getJDivision ();
            
            eq = Equality.EQUALS;
            leq = numbers.getLessOrEquals ();
            geq = numbers.getGreaterOrEquals ();
            
            intS = numbers.getNumberSymbol ().sort ();
            
            intF = extendsTrans ( intS );
            
            addF = op(add);
            mulF = op(mul);
            modF = op(mod);
            divF = op(div);
            jmodF = op(jmod);
            jdivF = op(jdiv);
            
            eqF = op(eq);
            geqF = op(geq);
            leqF = op(leq);

            literal =
                op ( Z );
            negLiteral =
                opSub ( Z, op ( numbers.getNegativeNumberSign() ) );
            nonNegLiteral =
                opSub ( Z, not ( op ( numbers.getNegativeNumberSign() ) ) );
            zeroLiteral =
                opSub ( Z, opSub ( numbers.getNumberLiteralFor ( 0 ), 
                                   op ( numbers.getNumberTerminator () ) ) );
            oneLiteral =
                opSub ( Z, opSub ( numbers.getNumberLiteralFor ( 1 ), 
                                   op ( numbers.getNumberTerminator () ) ) );
            nonPosLiteral = or ( zeroLiteral, negLiteral );
            posLiteral = add ( nonNegLiteral, not ( zeroLiteral ) );
            atLeastTwoLiteral = add ( posLiteral, not ( oneLiteral ) );

            atom = add ( not ( addF ), not ( mulF ) );
            linearMonomial = or ( atom, opSub ( mul, atom, literal ) );
            
            // left-associatively arranged monomials, literals are only allowed
            // as right-most term
            monomial =
                or ( atom,
                     opSub ( mul,
                             rec ( mulF, or ( opSub ( mul, any (), not ( mulF ) ),
                                              add ( not ( addF ), not ( literal ) ) ) ),
                             atom ) );

            // left-associatively arranged polynomials
            polynomial = rec ( addF, or ( opSub ( add, any (), not ( addF ) ),
                                          monomial ) );
                  
            nonNegMonomial = add ( monomial,
                                   or ( not ( mulF ),
                                        sub ( any (), not ( negLiteral ) ) ) );
            posMonomial = opSub ( mul, monomial, posLiteral );            
            negMonomial = opSub ( mul, monomial, negLiteral );            
            nonCoeffMonomial = add ( monomial,
                                     or ( not ( mulF ),
                                          sub ( any (), not ( literal ) ) ) );
            nonNegOrNonCoeffMonomial =
                add ( monomial,
                      or ( not ( mulF ),
                           sub ( any (), not ( negLiteral ) ) ) );
            atLeastTwoCoeffMonomial = opSub ( mul, monomial, atLeastTwoLiteral );
            
            intEquation = opSub ( eq, add ( intF, nonNegMonomial ),
                                  add ( intF, polynomial ) );
            linearEquation = opSub ( eq, linearMonomial,
                                     add ( intF, polynomial ) );
            monomialEquation = opSub ( eq, add ( intF, nonNegMonomial ),
                                       add ( intF, monomial ) );
            intInEquation = add ( or ( leqF, geqF ),
                                  sub ( nonNegMonomial, polynomial ) );
            linearInEquation = add ( or ( leqF, geqF ),
                                     sub ( linearMonomial, polynomial ) );
            intRelation = add ( or ( leqF, geqF, eqF ),
                                sub ( add ( intF, nonNegMonomial), polynomial ) );
            
            notContainsProduct =
                rec ( any (),
                      ifZero ( mulF,
                               not ( sub ( not ( literal ), not ( literal ) ) ) ) );
            notContainsDivMod = rec ( any (),
                                      add ( add ( not ( divF ), not ( modF ) ),
                                            add ( not ( jdivF ), not ( jmodF ) ) ) );
        }
        
        final Sort intS;

        final Function Z;
        final Function add;        
        final Function mul;
        final Function mod;
        final Function div;
        final Function jmod;
        final Function jdiv;

        final Operator eq;
        final Function leq;
        final Function geq;
        
        final TermFeature intF;
        
        final TermFeature addF;
        final TermFeature mulF;
        final TermFeature modF;
        final TermFeature divF;
        final TermFeature jmodF;
        final TermFeature jdivF;

        final TermFeature eqF;
        final TermFeature leqF;
        final TermFeature geqF;

        final TermFeature atom;
        final TermFeature linearMonomial;
        
        // left-associatively arranged monomials
        final TermFeature monomial;
        // left-associatively arranged polynomials
        final TermFeature polynomial;
              
        final TermFeature literal;
        final TermFeature posLiteral;
        final TermFeature negLiteral;
        final TermFeature nonNegLiteral;
        final TermFeature nonPosLiteral;
        final TermFeature zeroLiteral;
        final TermFeature oneLiteral;
        final TermFeature atLeastTwoLiteral;

        final TermFeature nonNegMonomial;
        final TermFeature posMonomial;
        final TermFeature negMonomial;
        final TermFeature nonCoeffMonomial;
        final TermFeature nonNegOrNonCoeffMonomial;
        final TermFeature atLeastTwoCoeffMonomial;
        
        final TermFeature intEquation;
        final TermFeature linearEquation;
        final TermFeature monomialEquation;
        final TermFeature intInEquation;
        final TermFeature linearInEquation;
        final TermFeature intRelation;
        
        final TermFeature notContainsProduct;
        final TermFeature notContainsDivMod;
    }

    private class FormulaTermFeatures {

        public FormulaTermFeatures () {
            forF = extendsTrans ( Sort.FORMULA );
            
            orF = op ( Junctor.OR );
            andF = op ( Junctor.AND );
            impF = op ( Junctor.IMP );
            notF = op ( Junctor.NOT );
            ifThenElse = OperatorClassTF.create ( IfThenElse.class );
            
            query = OperatorClassTF.create ( ProgramMethod.class );
            
            atom = AtomTermFeature.INSTANCE;
            propJunctor = or ( OperatorClassTF.create ( Junctor.class ),
                               op ( Equality.EQV ) );
            literal = or ( atom, opSub ( Junctor.NOT, atom ) );
            
            // left-associatively arranged clauses
            clause = rec ( orF, or ( opSub ( Junctor.OR, any (), not ( orF ) ),
                                     literal ) ); 

            // left-associatively arranged sets of clauses
            clauseSet = rec ( andF, or ( opSub ( Junctor.AND, any (), not ( andF ) ),
                                         clause ) ); 

            quantifiedFor = or ( op ( Quantifier.ALL ), op ( Quantifier.EX ) );
            quantifiedClauseSet = rec ( quantifiedFor,
                                        or ( quantifiedFor, clauseSet ) );
            
            quantifiedAnd = rec ( quantifiedFor,
                                  or ( quantifiedFor, andF ) );
            quantifiedOr = rec ( quantifiedFor,
                                 or ( quantifiedFor, orF ) );
            
            // conjunction or disjunction of literals, without and-or alternation
            pureLitConjDisj = or ( rec ( andF, or ( andF, literal ) ),
                                   rec ( orF, or ( orF, literal ) ) );
            quantifiedPureLitConjDisj = rec ( quantifiedFor,
                                              or ( quantifiedFor, pureLitConjDisj ) );
            
            update = OperatorClassTF.create ( UpdateApplication.class );
            program = OperatorClassTF.create ( Modality.class );
            modalOperator = or ( update, program );
            
//            directCutAllowed = add ( atom, not ( modalOperator ) );
            notExecutable =
                expandQueries () ?
                add ( not ( program ), not ( query ) ) : not ( program );
            notContainsExecutable = rec ( any (), notExecutable );
            
            cutAllowed =
                add ( notContainsExecutable,
                      tf.notContainsProduct,
                      or ( tf.eqF,
                           OperatorClassTF.create ( SortedOperator.class ) ) );
            cutAllowedBelowQuantifier = add ( not ( propJunctor ),
                                              notContainsExecutable );
            cutPriority = add ( ifZero ( tf.intInEquation,
                                         longTermConst ( 0 ),
                                ifZero ( tf.eqF,
                                         longTermConst ( 100 ),
                                         longTermConst ( 200 ) ) ),
                                rec ( any (), longTermConst ( 1 ) ) );
//            directCutAllowed = add ( tf.intInEquation, notContainsQuery );
        }

        final TermFeature forF;

        final TermFeature orF;
        final TermFeature andF;
        final TermFeature impF;
        final TermFeature notF;
        final TermFeature propJunctor;
        final TermFeature ifThenElse;
        final TermFeature query;
        final TermFeature notExecutable;
        final TermFeature notContainsExecutable;

        final TermFeature quantifiedFor;
        final TermFeature quantifiedOr;
        final TermFeature quantifiedAnd;

        final TermFeature atom;
        final TermFeature literal;
        final TermFeature clause;
        final TermFeature clauseSet;
        final TermFeature quantifiedClauseSet;

        final TermFeature pureLitConjDisj;
        final TermFeature quantifiedPureLitConjDisj;
        
        final TermFeature update;
        final TermFeature program;
        final TermFeature modalOperator;
        
        final TermFeature cutAllowed;
        final TermFeature cutAllowedBelowQuantifier;
        final TermFeature cutPriority;
    }
}
