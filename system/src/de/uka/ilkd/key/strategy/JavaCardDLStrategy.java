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

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.rule.QueryExpand;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.rule.UseOperationContractRule;
import de.uka.ilkd.key.rule.WhileInvariantRule;
import de.uka.ilkd.key.strategy.definition.AbstractStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.OneOfStrategyPropertyDefinition;
import de.uka.ilkd.key.strategy.definition.StrategyPropertyValueDefinition;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.AgeFeature;
import de.uka.ilkd.key.strategy.feature.AllowedCutPositionFeature;
import de.uka.ilkd.key.strategy.feature.AtomsSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.AutomatedRuleFeature;
import de.uka.ilkd.key.strategy.feature.CheckApplyEqFeature;
import de.uka.ilkd.key.strategy.feature.ConditionalFeature;
import de.uka.ilkd.key.strategy.feature.ContainsTermFeature;
import de.uka.ilkd.key.strategy.feature.CountMaxDPathFeature;
import de.uka.ilkd.key.strategy.feature.CountPosDPathFeature;
import de.uka.ilkd.key.strategy.feature.DependencyContractFeature;
import de.uka.ilkd.key.strategy.feature.DiffFindAndIfFeature;
import de.uka.ilkd.key.strategy.feature.DiffFindAndReplacewithFeature;
import de.uka.ilkd.key.strategy.feature.DirectlyBelowSymbolFeature;
import de.uka.ilkd.key.strategy.feature.EqNonDuplicateAppFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.FindDepthFeature;
import de.uka.ilkd.key.strategy.feature.FindRightishFeature;
import de.uka.ilkd.key.strategy.feature.FocusInAntecFeature;
import de.uka.ilkd.key.strategy.feature.InEquationMultFeature;
import de.uka.ilkd.key.strategy.feature.MatchedIfFeature;
import de.uka.ilkd.key.strategy.feature.MonomialsSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.NoSelfApplicationFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppModPositionFeature;
import de.uka.ilkd.key.strategy.feature.NotBelowBinderFeature;
import de.uka.ilkd.key.strategy.feature.NotBelowQuantifierFeature;
import de.uka.ilkd.key.strategy.feature.NotInScopeOfModalityFeature;
import de.uka.ilkd.key.strategy.feature.OnlyInScopeOfQuantifiersFeature;
import de.uka.ilkd.key.strategy.feature.PolynomialValuesCmpFeature;
import de.uka.ilkd.key.strategy.feature.PurePosDPathFeature;
import de.uka.ilkd.key.strategy.feature.QueryExpandCost;
import de.uka.ilkd.key.strategy.feature.ReducibleMonomialsFeature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.ScaleFeature;
import de.uka.ilkd.key.strategy.feature.SeqContainsExecutableCodeFeature;
import de.uka.ilkd.key.strategy.feature.SetsSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.SumFeature;
import de.uka.ilkd.key.strategy.feature.TermSmallerThanFeature;
import de.uka.ilkd.key.strategy.feature.ThrownExceptionFeature;
import de.uka.ilkd.key.strategy.feature.TopLevelFindFeature;
import de.uka.ilkd.key.strategy.feature.TrivialMonomialLCRFeature;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesSmallerThanFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EliminableQuantifierTF;
import de.uka.ilkd.key.strategy.quantifierHeuristics.HeuristicInstantiation;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCost;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCostScalerFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.LiteralsSmallerThanFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.SplittableQuantifiedFormulaFeature;
import de.uka.ilkd.key.strategy.termProjection.AssumptionProjection;
import de.uka.ilkd.key.strategy.termProjection.CoeffGcdProjection;
import de.uka.ilkd.key.strategy.termProjection.DividePolynomialsProjection;
import de.uka.ilkd.key.strategy.termProjection.FocusFormulaProjection;
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;
import de.uka.ilkd.key.strategy.termProjection.MonomialColumnOp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;
import de.uka.ilkd.key.strategy.termProjection.ReduceMonomialsProjection;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termfeature.AnonHeapTermFeature;
import de.uka.ilkd.key.strategy.termfeature.AtomTermFeature;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termfeature.IsNonRigidTermFeature;
import de.uka.ilkd.key.strategy.termfeature.IsSelectSkolemConstantTermFeature;
import de.uka.ilkd.key.strategy.termfeature.OperatorClassTF;
import de.uka.ilkd.key.strategy.termfeature.OperatorTF;
import de.uka.ilkd.key.strategy.termfeature.PrimitiveHeapTermFeature;
import de.uka.ilkd.key.strategy.termfeature.SimplifiedSelectTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;
import de.uka.ilkd.key.strategy.termgenerator.AllowedCutPositionsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.MultiplesModEquationsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.RootsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SequentFormulasGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SubtermGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;
import de.uka.ilkd.key.strategy.termgenerator.TriggeredInstantiations;
import de.uka.ilkd.key.util.MiscTools;


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

    private final HeapLDT heapLDT;
    
    protected final RuleSetDispatchFeature getCostComputationDispatcher() {
        return costComputationDispatcher;
    }

    protected final RuleSetDispatchFeature getInstantiationDispatcher() {
        return instantiationDispatcher;
    }

    protected final StrategyProperties strategyProperties;
    
    protected JavaCardDLStrategy(Proof p_proof,
                                 StrategyProperties strategyProperties) {
        
        super ( p_proof );
        heapLDT = p_proof.getServices().getTypeConverter().getHeapLDT();
        
        this.strategyProperties =
            (StrategyProperties)strategyProperties.clone ();
      
        this.tf = new ArithTermFeatures ( p_proof.getServices ()
                                          .getTypeConverter ().getIntegerLDT () );
        this.ff = new FormulaTermFeatures ();        
        this.vf = new ValueTermFeature();
        
        costComputationDispatcher = setupCostComputationF ( p_proof );
        approvalDispatcher = setupApprovalDispatcher ( p_proof );
        instantiationDispatcher = setupInstantiationF ( p_proof );
        
        costComputationF = setupGlobalF ( costComputationDispatcher, p_proof );
        instantiationF = setupGlobalF ( instantiationDispatcher, p_proof );
        approvalF = add ( setupApprovalF ( p_proof ), approvalDispatcher );
    }    
    
    
    protected Feature setupGlobalF(Feature dispatcher, Proof p_proof) {//        
        final Feature ifMatchedF = ifZero ( MatchedIfFeature.INSTANCE,
                                            longConst ( +1 ) );
        
//        final Feature splitF =
//            ScaleFeature.createScaled ( CountBranchFeature.INSTANCE, 50);

//        final Feature strengthenConstraints =
//            ifHeuristics ( new String[] { "concrete", "closure" },
//                           longConst ( 0 ),
//                           ifZero ( ConstraintStrengthenFeatureUC.create ( p_proof ),
//                                    inftyConst () ) );
        
        final Feature methodSpecF;
        final String methProp 
        	= strategyProperties.getProperty(
        		StrategyProperties.METHOD_OPTIONS_KEY);        
        if(methProp.equals(StrategyProperties.METHOD_CONTRACT)) {   
            methodSpecF = methodSpecFeature(longConst(-20));
        } else if(methProp.equals(StrategyProperties.METHOD_EXPAND)) {  
            methodSpecF = methodSpecFeature(inftyConst());
        } else if(methProp.equals(StrategyProperties.METHOD_NONE)) {   
            methodSpecF = methodSpecFeature(inftyConst());
        } else {
            methodSpecF = null;
            assert false;
        }

        final String queryProp = strategyProperties.getProperty(StrategyProperties.QUERY_OPTIONS_KEY);
        final Feature queryF;
        if (queryProp.equals(StrategyProperties.QUERY_ON)) {
       	    queryF = querySpecFeature(new QueryExpandCost(200,1,1,false)); 
        } else if (queryProp.equals(StrategyProperties.QUERY_RESTRICTED)) {
        	// All tests in the example directory pass with this strategy. 
        	//Hence, the old query_on strategy is obsolete.
    	    queryF = querySpecFeature(new QueryExpandCost(500,0,20,true));  
        } else if (queryProp.equals(StrategyProperties.QUERY_OFF)) {
        	queryF = querySpecFeature(inftyConst());
        } else {
                queryF = null;
                assert false;
        }
        

        final Feature depSpecF;
        final String depProp
        	= strategyProperties.getProperty(
        		StrategyProperties.DEP_OPTIONS_KEY);
        final SetRuleFilter depFilter = new SetRuleFilter();
        depFilter.addRuleToSet(UseDependencyContractRule.INSTANCE);
        if (depProp.equals(StrategyProperties.DEP_ON)) {
                depSpecF = ConditionalFeature.createConditional(depFilter,
                                                                longConst(400));
        } else {
            depSpecF = ConditionalFeature.createConditional(depFilter,
        	    					    inftyConst());
        }
        
        final Feature loopInvF;
        final String loopProp
        	= strategyProperties.getProperty(
        		StrategyProperties.LOOP_OPTIONS_KEY);
        if(loopProp.equals(StrategyProperties.LOOP_INVARIANT)) {
            loopInvF = loopInvFeature(longConst(0));
        } else {
            loopInvF = loopInvFeature(inftyConst());
        }
        
        final Feature blockFeature;
        final String blockProperty = strategyProperties.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY);
        if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT)) {
        	blockFeature = blockContractFeature(longConst(Long.MIN_VALUE));
        }
        else {
        	blockFeature = blockContractFeature(inftyConst());
        }
        
        final Feature oneStepSimplificationF 
        	= oneStepSimplificationFeature(longConst(-11000));
      //  final Feature smtF = smtFeature(inftyConst());
        
        return SumFeature.createSum (AutomatedRuleFeature.INSTANCE,
              NonDuplicateAppFeature.INSTANCE,
//              splitF,
//              strengthenConstraints, 
              AgeFeature.INSTANCE,
              oneStepSimplificationF,
             // smtF, 
              methodSpecF, 
              queryF,
              depSpecF,
              loopInvF,
              blockFeature,
              ifMatchedF,
                dispatcher);
    }
    
    private Feature loopInvFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(WhileInvariantRule.INSTANCE);
	return ConditionalFeature.createConditional(filter, cost);
    }
    
    private Feature blockContractFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(BlockContractRule.INSTANCE);
	return ConditionalFeature.createConditional(filter, cost);
    }

    private Feature methodSpecFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(UseOperationContractRule.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);        
    }

    private Feature querySpecFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(QueryExpand.INSTANCE);
        return ConditionalFeature.createConditional(filter, cost);        
    }

    private Feature oneStepSimplificationFeature(Feature cost) {
	SetRuleFilter filter = new SetRuleFilter();
	filter.addRuleToSet(MiscTools.findOneStepSimplifier(getProof()));
	return ConditionalFeature.createConditional(filter, cost);
    }


    //private Feature smtFeature(Feature cost) {
	//ClassRuleFilter filter = new ClassRuleFilter(SMTRule.class);
        //return ConditionalFeature.createConditional(filter, cost);        
   // }       
    
  //  private Feature smtMultiFeature(Feature cost) {
	//ClassRuleFilter filter = new ClassRuleFilter(SMTRuleMulti.class);
     //   return ConditionalFeature.createConditional(filter, cost);        
   //}       

    
    
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the computation of costs for taclet applications
    //
    ////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////

    
    private RuleSetDispatchFeature setupCostComputationF(Proof p_proof) {
        final Services services = p_proof.getServices();
        final IntegerLDT numbers =
            services.getTypeConverter().getIntegerLDT();
        final LocSetLDT locSetLDT =
                services.getTypeConverter().getLocSetLDT();
            
        final RuleSetDispatchFeature d = RuleSetDispatchFeature.create ();
           
        bindRuleSet ( d, "semantics_blasting", inftyConst () );
        
        bindRuleSet ( d, "closure", -15000 );
        bindRuleSet ( d, "alpha", -7000 );
        bindRuleSet ( d, "delta", -6000 );
        bindRuleSet ( d, "simplify_boolean", -200 );
        
        bindRuleSet ( d, "concrete", 
                add( longConst(-11000), 
                     ScaleFeature.createScaled ( FindDepthFeature.INSTANCE, 10.0 ) ) );        
        bindRuleSet ( d, "simplify", -4500 );        
        bindRuleSet ( d, "simplify_enlarging", -2000 );
        bindRuleSet ( d, "simplify_expression", -100 );
        bindRuleSet ( d, "executeIntegerAssignment", -100 );

        bindRuleSet ( d, "javaIntegerSemantics", -5000 );
        
        // always give infinite cost to obsolete rules
        bindRuleSet (d, "obsolete", inftyConst());


        setupSelectSimplification(d);

        bindRuleSet (d, "update_elim",
                add( longConst(-8000), ScaleFeature.createScaled ( FindDepthFeature.INSTANCE, 10.0 ) ) ); 
        bindRuleSet (d, "update_apply_on_update", 
                add( longConst(-7000), ScaleFeature.createScaled ( FindDepthFeature.INSTANCE, 10.0 ) ) );
        bindRuleSet (d, "update_join", -4600);
        bindRuleSet (d, "update_apply", -4500);
             
        setUpStringNormalisation ( d, services );
        
        setupSplitting ( d );

        bindRuleSet ( d, "test_gen", inftyConst () );
        bindRuleSet ( d, "test_gen_empty_modality_hide", inftyConst () );
        bindRuleSet ( d, "test_gen_quan", inftyConst () );
        bindRuleSet ( d, "test_gen_quan_num", inftyConst () );

        bindRuleSet ( d, "gamma",
                      add ( not ( isInstantiated ( "t" ) ),
                            ifZero ( allowQuantifierSplitting (),
                                     longConst ( 0 ), longConst ( 50 ) ) ) );
        bindRuleSet ( d, "gamma_destructive", inftyConst () );

        bindRuleSet (d, "triggered", 
                add( not ( isTriggerVariableInstantiated() ), longConst(500) ) );
        
        bindRuleSet ( d, "comprehension_split",
                add (   applyTF ( FocusFormulaProjection.INSTANCE, ff.notContainsExecutable ),
                        ifZero( allowQuantifierSplitting(), longConst(2500), longConst( 5000 ) ) ) );
        
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
//                      ifZero ( ConstraintStrengthenFeatureUC.create(p_proof),
//                               longConst ( 0 ),
                               longConst ( -8000 ) );
        
        bindRuleSet ( d, "simplify_instanceof_static",
                      add ( EqNonDuplicateAppFeature.INSTANCE,
                            longConst ( -500 ) ) );

        bindRuleSet ( d, "comprehensions",
                      add ( NonDuplicateAppModPositionFeature.INSTANCE,
                            longConst ( -100 ) ) );
        
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
           add ( sum ( superFor, SuperTermGenerator.upwards ( any (), services ),
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
                                                   services ),
                    longConst ( 500 ),
                    ifZero ( isBelow ( add ( ff.forF, not ( ff.atom ) ), services ),
                             longConst ( 200 ), longConst ( -100 ) ) ) );
                
        
        bindRuleSet (d, "simplify_prog_subset",	longConst(-4000));
        bindRuleSet (d, "modal_tautology",	longConst(-10000));
        
        // features influenced by the strategy options
        
        boolean useLoopExpand = strategyProperties.getProperty(
                StrategyProperties.LOOP_OPTIONS_KEY).
                    equals(StrategyProperties.LOOP_EXPAND);
        /*boolean useBlockExpand = strategyProperties.getProperty(
                StrategyProperties.BLOCK_OPTIONS_KEY).
                    equals(StrategyProperties.BLOCK_EXPAND);*/
        boolean programsToRight = true;//XXX
        
        final String methProp
        	= strategyProperties.getProperty(
        			StrategyProperties.METHOD_OPTIONS_KEY);
        if (methProp.equals(StrategyProperties.METHOD_CONTRACT)) {
        	/* If method treatment by contracts is chosen, this does not mean 
        	 * that method expansion is disabled. The original cost was 200 
        	 * and is now increased to 2000 in order to repress method expansion 
        	 * stronger when method treatment by contracts is chosen. 
        	 */
            bindRuleSet(d, "method_expand", longConst(2000));   	
        	//bindRuleSet(d, "method_expand", inftyConst()); //This seems to be more correct, but the then some proofs from the example directory do not work.
        } else if (methProp.equals(StrategyProperties.METHOD_EXPAND)) {
            bindRuleSet(d, "method_expand", longConst(100));	   
        } else if (methProp.equals(StrategyProperties.METHOD_NONE)) {
            bindRuleSet(d, "method_expand", inftyConst());	  
        } else throw new RuntimeException("Unexpected strategy property "+
                                          methProp);

        
        final String queryAxProp = strategyProperties.
                           getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
        if (queryAxProp.equals(StrategyProperties.QUERYAXIOM_ON)) {
            bindRuleSet ( d, "query_axiom", longConst(-3000) ); //Originally the QueryAxiom rule was assigned the strategy "simplify". Hence, the cost should be probably low.
        } else if (queryAxProp.equals(StrategyProperties.QUERYAXIOM_OFF)) {
            bindRuleSet ( d, "query_axiom", inftyConst());
        } else {
                assert false;
        }
        
        bindRuleSet ( d, "loop_expand",
                      useLoopExpand ? longConst ( 0 )
                                    : inftyConst () );
        
        /*bindRuleSet ( d, "block_expand",
                      useBlockExpand ? longConst ( 0 )
                                     : inftyConst () );*/
        
        // delete cast
        bindRuleSet ( d, "cast_deletion",
                      ifZero ( implicitCastNecessary ( instOf ( "castedTerm" ) ),
                               longConst ( -5000 ), inftyConst () ) );
        
       

        bindRuleSet ( d, "type_hierarchy_def", -6500 );
        
        //partial inv axiom
        bindRuleSet ( d, "partialInvAxiom",
                      add ( NonDuplicateAppModPositionFeature.INSTANCE,
                            longConst ( 10000 ) ) );

        //inReachableState        
        bindRuleSet ( d, "inReachableStateImplication",
                      add ( NonDuplicateAppModPositionFeature.INSTANCE,
                            longConst ( 100 ) ) );
        
        //class axioms
        final String classAxiomPrio = strategyProperties.getProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY);
        final Feature classAxiomDefaultCost = longConst(-150);
        if (StrategyProperties.CLASS_AXIOM_FREE.equals(classAxiomPrio))
            // default as before
            bindRuleSet ( d, "classAxiom", classAxiomDefaultCost );
        else if (StrategyProperties.CLASS_AXIOM_DELAYED.equals(classAxiomPrio))
            bindRuleSet(d, "classAxiom", add (sequentContainsNoPrograms(), classAxiomDefaultCost ));
        else if (StrategyProperties.CLASS_AXIOM_OFF.equals(classAxiomPrio))
            bindRuleSet(d, "classAxiom", inftyConst());
        else assert false : "Unknown strategy property "+classAxiomPrio;
                
        //limit observer (must have better priority than "classAxiom")
        bindRuleSet ( d, "limitObserver",
                      add ( NonDuplicateAppModPositionFeature.INSTANCE,
                            longConst ( -200 ) ) );                
                        
        if ( programsToRight )
            bindRuleSet ( d, "boxDiamondConv",
                          SumFeature.createSum (
                                new FindPrefixRestrictionFeature(
                                      FindPrefixRestrictionFeature.PositionModifier.ALLOW_UPDATE_AS_PARENT,
                                      FindPrefixRestrictionFeature.PrefixChecker.ANTEC_POLARITY),
                                longConst(-1000)));
        else
            bindRuleSet ( d, "boxDiamondConv", inftyConst () );
        
        bindRuleSet ( d, "cut", not ( isInstantiated ( "cutFormula" ) ) );

        setupUserTaclets ( d );
        
        setupArithPrimaryCategories ( d );
        setupPolySimp ( d, numbers );        
        setupInEqSimp ( d, p_proof, numbers );
        
        setupDefOpsPrimaryCategories ( d, services );
        
        setupSystemInvariantSimp(d);
               
        
        if ( quantifierInstantiatedEnabled() ) {
            setupFormulaNormalisation (d, numbers, locSetLDT, services);
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
        
        //chrisg: The following rule, if active, must be applied delta rules.
        if(autoInductionEnabled()){
        	bindRuleSet ( d, "auto_induction", -6500 ); //chrisg
        }else{
        	bindRuleSet ( d, "auto_induction", inftyConst () ); //chrisg
        }
        
        //chrisg: The following rule is a beta rule that, if active, must have a higher priority than other beta rules.
        if(autoInductionLemmaEnabled()){
        	bindRuleSet ( d, "auto_induction_lemma", -300 ) ; 
        }else{
            bindRuleSet ( d, "auto_induction_lemma", inftyConst());        	
        }

        
        return d;
    }

    private void setupSelectSimplification(final RuleSetDispatchFeature d) {
        bindRuleSet ( d, "pull_out_select",
                      // pull out select only if it can be simplified
                      // (the heap term may not be the base heap or an anon heap
                      // function symbol)
                      add( applyTF( "h", not( or( PrimitiveHeapTermFeature.create(heapLDT),
                                                  AnonHeapTermFeature.INSTANCE ) ) ),
                           ifZero( applyTF(FocusFormulaProjection.INSTANCE, ff.update),
                                   longConst(-4200),
                                   longConst(-1900) ),
                           NonDuplicateAppModPositionFeature.INSTANCE ) );
        bindRuleSet ( d, "apply_select_eq",
                      // replace non-simplified select by the skolem constant
                      // of the corresponding pull out; at least one select
                      // needs to be not simplified yet; additional restrictions
                      // in isApproved()
                      ifZero( applyTF( "s",
                                      not( rec( any(), SimplifiedSelectTermFeature.create(heapLDT) ) ) ),
                             // together with the costs of apply_equations the
                             // resulting costs are about -5700
                             longConst(-1700) ) );
        bindRuleSet ( d, "simplify_select",
                      // simplify_select term in pulled out equation (right hand
                      // side has to be a skolem constant which has been
                      // introduced by a select pull out; left hand side needs
                      // to be a select term on a non-base- and
                      // non-anon-heap)
                      add( applyTF("sk", IsSelectSkolemConstantTermFeature.INSTANCE),
                           applyTF( sub( FocusProjection.INSTANCE, 0),
                                    not( SimplifiedSelectTermFeature.create(heapLDT) ) ),
                           longConst(-5600) ) );
        bindRuleSet ( d, "apply_auxiliary_eq",
                      // replace skolem constant by it's computed value
                      add( applyTF("t1", IsSelectSkolemConstantTermFeature.INSTANCE),
                           longConst(-5500) ) );
        bindRuleSet ( d, "hide_auxiliary_eq",
                      // hide auxiliary equation after the skolem constatns have
                      // been replaced by it's computed value
                      add( applyTF( "auxiliarySK", IsSelectSkolemConstantTermFeature.INSTANCE),
                           applyTF( "result", rec( any(), add( SimplifiedSelectTermFeature.create(heapLDT),
                                                               not( ff.ifThenElse ) ) ) ),
                           not( ContainsTermFeature.create( instOf("result"),
                                                            instOf("auxiliarySK") ) ),
                           longConst(-5400) ) );
        bindRuleSet ( d, "hide_auxiliary_eq_const",
                      // hide auxiliary equation after the skolem constatns have
                      // been replaced by it's computed value
                      add( applyTF("auxiliarySK", IsSelectSkolemConstantTermFeature.INSTANCE),
                           longConst(-500) ) );
    }

    private void setUpStringNormalisation (RuleSetDispatchFeature d, Services services) {
    
	// translates an integer into its string representation
	bindRuleSet ( d, "integerToString", -10000);
	
	
	// do not convert char to int when inside a string function
	// feature used to recognize if one is inside a string literal
        final CharListLDT charListLDT = services.getTypeConverter().getCharListLDT();
	
        final TermFeature keepChar = or ( 
		or ( OperatorTF.create( charListLDT.getClCons() ), 
		     OperatorTF.create( charListLDT.getClCharAt() ), 
		     OperatorTF.create(  charListLDT.getClIndexOfChar() ) ), 
		OperatorTF.create( charListLDT.getClLastIndexOfChar() ));
        
	final TermFeature emptyF = OperatorTF.create( charListLDT.getClEmpty() );
	
	bindRuleSet ( d, "charLiteral_to_intLiteral",
		ifZero ( isBelow ( keepChar, services ), inftyConst (), longConst (-100) ) ); 
	
	
	// establish normalform 

	// tf below only for test
	final TermFeature stringLiteral = rec ( any(), or ( or ( op (charListLDT.getClEmpty()), 
		                                op ( charListLDT.getClCons() ) ), tf.charLiteral) );

	Feature belowModOpPenality = ifZero  ( isBelow ( ff.modalOperator, services ),
		  longConst ( 500 ) );	


	Feature ignoreDefOpsCharAtLetSymbols = 
	    ifZero ( DirectlyBelowSymbolFeature.create(tf.eq, 0),
		ifZero (IntroducedSymbolBy.create(sub(FocusProjection.create(1), 1), 
			"defOpsCharAt", "newSym"), inftyConst()));

	bindRuleSet ( d, "defOpsCharAt",
		SumFeature.createSum ( new Feature[] {			
			NonDuplicateAppModPositionFeature.INSTANCE, 
				applyTF ("pos", not ( tf.zeroLiteral ) ),
				applyTF ("str", not ( emptyF ) ),
				ignoreDefOpsCharAtLetSymbols,
				longConst (5000),
				belowModOpPenality } ) ) ;

	bindRuleSet ( d, "defOpsStringEqualityInline", 
		add ( longConst (100) ,
		      ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 10) )
	);
		
	bindRuleSet ( d, "defOpsStringEquality",
		add ( NonDuplicateAppModPositionFeature.INSTANCE,
			ifZero (
			  add ( applyTF ("leftStr", not ( stringLiteral ) ),
				applyTF ("rightStr", not ( stringLiteral ) ) ),
			longConst (1000), 
			inftyConst()
			), belowModOpPenality ) 
	);
		
	bindRuleSet ( d, "defOpsSubstringInlineBase",  
		ifZero ( applyTF ("idx", tf.nonNegLiteral ), 
			longConst (100), 
			inftyConst()		
		) );

	bindRuleSet ( d, "defOpsSubstringInlineStepCons", 
		ifZero ( applyTF ("endIdx", tf.posLiteral ),
			longConst (100), 
			inftyConst()		
		) );
	
	bindRuleSet ( d, "defOpsSubstringInline", 
		ifZero ( add ( applyTF ("startIdx", tf.posLiteral ), 
			       applyTF ("endIdx", tf.posLiteral ) ),
			longConst (100), 
			inftyConst()		
		) );

	Feature ignoreDefOpsSubLetSymbols = 
	    ifZero ( DirectlyBelowSymbolFeature.create(tf.eq, 0),
		ifZero (IntroducedSymbolBy.create(sub(FocusProjection.create(1), 1), 
			"defOpsSubstring", "newSym"), inftyConst()));
	
	bindRuleSet ( d, "defOpsSubstring", 
		add ( 
		  NonDuplicateAppModPositionFeature.INSTANCE,
		  ifZero ( add (
			     applyTF ("startIdx", tf.nonNegLiteral ), 
			     applyTF ("endIdx", tf.nonNegLiteral ),
			     applyTF ("str", stringLiteral ) ),
			  inftyConst (), add( ignoreDefOpsSubLetSymbols, longConst(1000))
		  ), belowModOpPenality)
	);
	
	bindRuleSet ( d, "stringsLengthReduce", 
		NonDuplicateAppModPositionFeature.INSTANCE
	);
	
	bindRuleSet ( d, "defOpsConcat",
		add( NonDuplicateAppModPositionFeature.INSTANCE,
		     ifZero 
		       ( or ( applyTF ("leftStr", not ( stringLiteral ) ),
		              applyTF ("rightStr", not ( stringLiteral ) ) ), 
		         longConst(1000)  
		         // concat is often introduced for construction purposes, we do not want to use its definition right at the beginning      
		       ), belowModOpPenality  ) 
	);
	
	
	bindRuleSet ( d, "stringsSimplify", longConst ( -5000 ) ); 
	
	bindRuleSet ( d, "stringsExpandLengthConcat", longConst ( -3000 ) ); 

	bindRuleSet ( d, "stringsLengthInvariant",  
		ifZero ( applyTF ( instOf("str"), stringLiteral ) , 
			inftyConst(), longConst (500) )	
	);	
	
	final TermFeature charOrIntLiteral = or(tf.charLiteral, 
			tf.literal, 
			add (OperatorClassTF.create(SortDependingFunction.class),//XXX: was CastFunctionSymbol.class
				sub(tf.literal))); 
	
	bindRuleSet ( d, "defOpsReplaceInline",
		ifZero ( add ( applyTF ("str", stringLiteral ),
		               applyTF ("searchChar", charOrIntLiteral ),
		               applyTF ("replChar", charOrIntLiteral ) ),
		         longConst(500) )
	);
	
	bindRuleSet ( d, "defOpsReplace",
		add( NonDuplicateAppModPositionFeature.INSTANCE,
		     ifZero 
		       ( or ( applyTF ("str", not ( stringLiteral ) ),
		              applyTF ("searchChar", not ( charOrIntLiteral ) ),
		              applyTF ("replChar", not ( charOrIntLiteral ) )
		              ), 
		         longConst(500), inftyConst()		         
		        ), belowModOpPenality ) 
	);
	
	
	bindRuleSet (d, "stringsReduceSubstring", 
	        add(NonDuplicateAppModPositionFeature.INSTANCE,
	        	longConst (100) ) );
	
	bindRuleSet (d, "defOpsStartsEndsWith", longConst (250) );


	bindRuleSet ( d, "stringsConcatNotBothLiterals",		
		ifZero ( MatchedIfFeature.INSTANCE,
		ifZero ( add ( 
			  applyTF ( instOf("leftStr"), stringLiteral ),
			  applyTF ( instOf("rightStr"), stringLiteral ) ), 
			inftyConst() ), inftyConst() ) ) ;	
	

	bindRuleSet ( d, "stringsReduceConcat", longConst (100) );
	

	bindRuleSet (d, "stringsReduceOrMoveOutsideConcat", 
		ifZero (NonDuplicateAppModPositionFeature.INSTANCE,
			longConst( 800 ), inftyConst()));
	
	bindRuleSet (d, "stringsMoveReplaceInside", 
		ifZero (NonDuplicateAppModPositionFeature.INSTANCE,
			longConst( 400 ), inftyConst()));
	
	bindRuleSet(d, "stringDiffIfFind", 
		ifZero ( MatchedIfFeature.INSTANCE,
                DiffFindAndIfFeature.INSTANCE ) );

	bindRuleSet ( d, "stringsExpandDefNormalOp", 
        	SumFeature.createSum ( new Feature[] { longConst(500) } ));
	
	bindRuleSet ( d, "stringsContainsDefInline", 
        	SumFeature.createSum ( new Feature[] {
        		EqNonDuplicateAppFeature.INSTANCE, longConst(1000) } ));
    }

    private void setupReplaceKnown(RuleSetDispatchFeature d) {
        final Feature commonF =
            add ( ifZero ( MatchedIfFeature.INSTANCE,
                           DiffFindAndIfFeature.INSTANCE ),
                  longConst ( -5000 ),
                  add(DiffFindAndReplacewithFeature.INSTANCE,
                      ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 ) ));

        bindRuleSet ( d, "replace_known_left", commonF );
        bindRuleSet ( d, "replace_known_right",
            add ( commonF,
                  ifZero ( DirectlyBelowSymbolFeature.create ( Junctor.IMP, 1 ),
                           longConst ( 100 ),
                  ifZero ( DirectlyBelowSymbolFeature.create ( Equality.EQV ),
                           longConst ( 100 ) ) ) ) );
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
        return not ( SeqContainsExecutableCodeFeature.PROGRAMS );
    }
    
    private boolean quantifierInstantiatedEnabled () {
        return !StrategyProperties.QUANTIFIERS_NONE.equals (
                 strategyProperties.getProperty
                 ( StrategyProperties.QUANTIFIERS_OPTIONS_KEY ) );
    }

    private boolean autoInductionEnabled () { //chrisg
    	//Negated!
        return !StrategyProperties.AUTO_INDUCTION_OFF.equals (
                 strategyProperties.getProperty
                 ( StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY ) );
    }

    private boolean autoInductionLemmaEnabled () {  //chrisg
    	final String prop =strategyProperties.getProperty
                             ( StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY ) ;
    	return prop.equals(StrategyProperties.AUTO_INDUCTION_LEMMA_ON) ||
    	       prop.equals(StrategyProperties.AUTO_INDUCTION_RESTRICTED);
    	/*
        return StrategyProperties.AUTO_INDUCTION_LEMMA_ON.equals (
                 strategyProperties.getProperty
                 ( StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY ) );
         */
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
          SumFeature.createSum (
             noCutsAllowed,
             ifZero ( PurePosDPathFeature.INSTANCE, longConst ( -200 ) ),
             ScaleFeature.createScaled ( CountPosDPathFeature.INSTANCE, -3.0 ),
             ScaleFeature.createScaled ( CountMaxDPathFeature.INSTANCE, 10.0 ),
             longConst ( 20 )
           ) );

        
        bindRuleSet ( d, "split_cond",
                      add ( // do not split over formulas containing auxiliary variables
                            applyTF ( FocusProjection.INSTANCE,
                                      rec ( any(),
                                            not ( IsSelectSkolemConstantTermFeature.INSTANCE ) ) ),
                            longConst ( 1 ) ) );

        bindRuleSet ( d, "cut_direct",
           SumFeature.createSum ( new Feature [] {
             not ( TopLevelFindFeature.ANTEC_OR_SUCC_WITH_UPDATE ),
             AllowedCutPositionFeature.INSTANCE,
             ifZero ( NotBelowQuantifierFeature.INSTANCE,
                      add ( applyTF ( "cutFormula",
                                      add ( ff.cutAllowed,
                                            // do not cut over formulas containing auxiliary variables
                                            rec ( any(),
                                                  not ( IsSelectSkolemConstantTermFeature.INSTANCE ) ) ) ),
                            // prefere cuts over "something = null"
                            ifZero ( add ( applyTF( FocusProjection.INSTANCE, tf.eqF ),
                                           applyTF( sub(FocusProjection.INSTANCE, 1), vf.nullTerm ) ),
                                     longConst ( -5 ),
                                     longConst ( 0 ) ),
                            // punish cuts over formulas containing anon heap functions
                            ifZero( applyTF( "cutFormula",
                                             rec ( any(),
                                                   not ( AnonHeapTermFeature.INSTANCE ) ) ),
                                    longConst ( 0 ),
                                    longConst ( 1000 ) ),
                            // standard costs
                            longConst ( 10 )),
                      SumFeature.createSum (
                            applyTF ( "cutFormula",
                                      ff.cutAllowedBelowQuantifier ),
                            applyTF ( FocusFormulaProjection.INSTANCE,
                                      ff.quantifiedClauseSet ),
                            ifZero ( allowQuantifierSplitting (),
                                       longConst ( 0 ), longConst ( 100 ) )) ) } ) );
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
                                           IntegerLDT numbers,
                                           LocSetLDT locSetLDT,
                                           Services services) {
       
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
                      ifZero(add ( or ( FocusInAntecFeature.INSTANCE,
                                        NotBelowQuantifierFeature.INSTANCE ),
                                   NotInScopeOfModalityFeature.INSTANCE),
                             add ( longConst ( -150 ),
                                   ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 20) ),
                             inftyConst() ) );

        bindRuleSet ( d, "setEqualityBlastingRight", longConst(-100) );

        bindRuleSet ( d, "cnf_setComm",
                      add ( SetsSmallerThanFeature.create(instOf("commRight"), instOf("commLeft"), locSetLDT),
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
                      SumFeature.createSum (
                           OnlyInScopeOfQuantifiersFeature.INSTANCE,
                           SplittableQuantifiedFormulaFeature.INSTANCE,
                           ifZero ( FocusInAntecFeature.INSTANCE,
                                    applyTF ( FocusProjection.create ( 0 ),
                                              sub ( ff.andF ) ),
                                    applyTF ( FocusProjection.create ( 0 ),
                                                 sub ( ff.orF ) ) )) ),
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
            sum ( superFor, SuperTermGenerator.upwards ( any (), services ),
                  applyTF ( superFor,
                            or ( ff.quantifiedFor, ff.andF, ff.orF ) ) );
        
        final Feature belowUnskolemisableQuantifier =
            ifZero ( FocusInAntecFeature.INSTANCE,
              not ( sum ( superFor,
                          SuperTermGenerator.upwards ( any (), services ),
                          not ( applyTF ( superFor, op ( Quantifier.ALL ) ) ) ) ),
              not ( sum ( superFor,
                          SuperTermGenerator.upwards ( any (), services ),
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
            final TermBuffer splitInst = new TermBuffer();
            
            
            bindRuleSet( d, "triggered", 
                    SumFeature.createSum(new Feature[]{                                                                                   
                            forEach( splitInst, TriggeredInstantiations.create(true),
                                    add (instantiateTriggeredVariable(splitInst), longConst(500))),
                                    longConst(1500)
                             }
                            ));        
            
        } else {
            bindRuleSet ( d, "gamma", inftyConst () );  
            bindRuleSet ( d, "triggered", inftyConst() );
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
            
            final TermBuffer splitInst = new TermBuffer ();
            bindRuleSet (d, "triggered", 
                    add ( isTriggerVariableInstantiated(), 
                    not ( sum ( splitInst, TriggeredInstantiations.create(false),
                            not ( eq ( instOfTriggerVariable (), splitInst ) ) ) ) ) );       
        } else {
            bindRuleSet ( d, "gamma", inftyConst () ); 
            bindRuleSet ( d, "triggered", inftyConst() );
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
              SumFeature.createSum (applyTF ( "newSymLeft", tf.atom ),
                applyTF ( "newSymLeftCoeff", tf.atLeastTwoLiteral ),
                applyTF ( "newSymRight", tf.polynomial ),
                instantiate ( "newSymDef",
                              MonomialColumnOp
                              .create ( instOf ( "newSymLeftCoeff" ),
                                            instOf("newSymRight")) )) ) );
        
        final TermBuffer divisor = new TermBuffer ();
        final TermBuffer dividend = new TermBuffer ();

        bindRuleSet ( d, "polySimp_applyEqPseudo",
           add (
             applyTF ( "aePseudoTargetLeft", tf.monomial ),
             applyTF ( "aePseudoTargetRight", tf.polynomial ),
             ifZero (MatchedIfFeature.INSTANCE,
               SumFeature.createSum (DiffFindAndIfFeature.INSTANCE,
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
                                           .create(dividend, divisor) ) ) ) )) ) ) );
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
                              PosInTerm.getTopLevel().down ( 0 ).down ( 0 ) ), numbers );
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
                      SumFeature.createSum (
                        applyTF ( "commRight", tf.monomial ),
                        applyTF ( "commLeft", tf.polynomial ),
                        monSmallerThan ( "commLeft", "commRight", numbers ),
                        longConst ( -40 ) ) );

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
                    SumFeature.createSum (
                      applyTFNonStrict ( "esCoeff1", tf.nonNegLiteral ),
                      applyTF ( "esRight1", tf.polynomial ),
                      not ( PolynomialValuesCmpFeature
                            .leq ( instOf ( "esRight2" ),
                                   instOf ( "esRight1" ),
                                   instOfNonStrict ( "esCoeff1" ),
                                   instOfNonStrict ( "esCoeff2" ) ))
                    ) ) } ) );

        // category "propagation"

        bindRuleSet ( d, "inEqSimp_contradInEqs",
           add ( applyTF ( "contradLeft", tf.monomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum (
                     DiffFindAndIfFeature.INSTANCE,
                     applyTF ( "contradRightSmaller", tf.polynomial ),
                     applyTF ( "contradRightBigger", tf.polynomial ),
                     applyTFNonStrict ( "contradCoeffSmaller", tf.posLiteral ),
                     applyTFNonStrict ( "contradCoeffBigger", tf.posLiteral ),
                     PolynomialValuesCmpFeature
                     .lt ( instOf ( "contradRightSmaller" ),
                           instOf ( "contradRightBigger" ),
                           instOfNonStrict ( "contradCoeffBigger" ),
                           instOfNonStrict ( "contradCoeffSmaller" ) ) ) ) ) );

        bindRuleSet ( d, "inEqSimp_contradEqs",
           add ( applyTF ( "contradLeft", tf.monomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum (
                     applyTF ( "contradRightSmaller", tf.polynomial ),
                     applyTF ( "contradRightBigger", tf.polynomial ),
                     PolynomialValuesCmpFeature
                     .lt ( instOf ( "contradRightSmaller" ),
                           instOf ( "contradRightBigger" ) ) ) ),
                 longConst ( -60 ) ) );

        bindRuleSet ( d, "inEqSimp_strengthen", longConst ( -30 ) );

        bindRuleSet ( d, "inEqSimp_subsumption",
           add ( applyTF ( "subsumLeft", tf.monomial ),
                 ifZero ( MatchedIfFeature.INSTANCE,
                   SumFeature.createSum (
                     DiffFindAndIfFeature.INSTANCE,
                     applyTF ( "subsumRightSmaller", tf.polynomial ),
                     applyTF ( "subsumRightBigger", tf.polynomial ),
                     applyTFNonStrict ( "subsumCoeffSmaller", tf.posLiteral ),
                     applyTFNonStrict ( "subsumCoeffBigger", tf.posLiteral ),
                     PolynomialValuesCmpFeature
                     .leq ( instOf ( "subsumRightSmaller" ),
                            instOf ( "subsumRightBigger" ),
                            instOfNonStrict ( "subsumCoeffBigger" ),
                            instOfNonStrict ( "subsumCoeffSmaller" ) ) ) ) ) );

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
        final TermServices services = p_proof.getServices ();
      one.setContent ( services.getTermBuilder().zTerm ( "1" ) );
        final TermBuffer two = new TermBuffer ();
        two.setContent ( services.getTermBuilder().zTerm ( "2" ) );

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
           add(applyTF("multLeft", tf.nonNegMonomial),
                   applyTF("multRight", tf.polynomial),
                   ifZero(MatchedIfFeature.INSTANCE,
                           SumFeature.createSum(
                                   applyTF("multFacLeft", tf.nonNegMonomial),
                                   ifZero(applyTF("multRight", tf.literal),
                                           longConst(-100)),
                                   ifZero(applyTF("multFacRight", tf.literal),
                                           longConst(-100),
                                           applyTF("multFacRight", tf.polynomial)),
/*                ifZero ( applyTF ( "multRight", tf.literal ),
                         longConst ( -100 ),
                         applyTF ( "multRight", tf.polynomial ) ),
                ifZero ( applyTF ( "multFacRight", tf.literal ),
                         longConst ( -100 ),
                         applyTF ( "multFacRight", tf.polynomial ) ), */
                                   not(TermSmallerThanFeature.create
                                           (FocusProjection.create(0),
                                                   AssumptionProjection.create(0))),
                                   ifZero(exactlyBounded,
                                           longConst(0),
                                           ifZero(totallyBounded,
                                                   longConst(100),
                                                   notAllowedF))
/*                                       ifZero ( partiallyBounded,
                                                longConst ( 400 ),
                                                notAllowedF ) ) ), */
/*                     applyTF ( "multLeft", rec ( tf.mulF, longTermConst ( 20 ) ) ),
                     applyTF ( "multFacLeft", rec ( tf.mulF, longTermConst ( 20 ) ) ),
                     applyTF ( "multRight", rec ( tf.addF, longTermConst ( 4 ) ) ),
                     applyTF ( "multFacRight", rec ( tf.addF, longTermConst ( 4 ) ) ), */
                           ),
                           notAllowedF)) );
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
              SumFeature.createSum (
                applyTF ( divisor, tf.nonCoeffMonomial ),
                not ( eq ( dividend, divisor ) ),
                applyTFNonStrict ( "divXBoundPos", tf.posLiteral ),
                applyTFNonStrict ( "divXBoundNeg", tf.negLiteral ),
                ReducibleMonomialsFeature.createReducible ( dividend, divisor ),
                instantiate ( "divY", ReduceMonomialsProjection
                                      .create ( dividend, divisor ) )
              ) ) ) )
          } ) );

        setupNonLinTermIsPosNeg ( d, "inEqSimp_nonLin_pos", true );
        setupNonLinTermIsPosNeg(d, "inEqSimp_nonLin_neg", false);
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
              SumFeature.createSum (
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
              ) ) ) )
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
        zero.setContent ( p_proof.getServices().getTermBuilder().zTerm ( "0" ) );
        final TermBuffer rootInf = new TermBuffer ();

        final Feature posNegSplitting =
           forEach ( intRel, SequentFormulasGenerator.antecedent (),
             add ( applyTF ( intRel, tf.intRelation ),
                   forEach ( atom,
                             SubtermGenerator.leftTraverse ( sub ( intRel, 0 ), tf.mulF ),
                      SumFeature.createSum (applyTF ( atom, add ( tf.atom, not ( tf.literal ) ) ),
                              allowPosNegCaseDistinction ( atom ),
                              instantiate ( "signCasesLeft", atom ),
                              longConst ( IN_EQ_SIMP_NON_LIN_COST + 200 )
//			            ,
//                      applyTF ( atom, rec ( any (), longTermConst ( 5 ) ) )
                      ) ) ) );
        
        bindRuleSet ( d, "inEqSimp_signCases", posNegSplitting ); 

        final Feature strengthening =
            forEach ( intRel, SequentFormulasGenerator.antecedent (),
              SumFeature.createSum (
                    applyTF ( intRel, add ( or ( tf.geqF, tf.leqF ),
                                            sub ( tf.atom, tf.literal ) ) ),
                    instantiate ( "cutFormula",
                                  opTerm ( tf.eq,
                                           sub ( intRel, 0 ), sub ( intRel, 1 ) ) ),
                    longConst ( IN_EQ_SIMP_NON_LIN_COST + 300 )
//		            ,
//                  applyTF ( sub ( intRel, 0 ),
//                            rec ( any (), longTermConst ( 5 ) ) )
              ) );
        
        final Feature rootInferences =
            forEach ( intRel, SequentFormulasGenerator.antecedent (),
              add ( isRootInferenceProducer ( intRel ),
                    forEach ( rootInf, RootsGenerator.create ( intRel, getProof().getServices() ),
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
        return applyTF(intRel, add(tf.intRelation,
                sub(tf.nonCoeffMonomial,
                        tf.literal)));
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
                                            RootsGenerator.create ( intRel, getProof().getServices() ),
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

    private void setupDefOpsPrimaryCategories(RuleSetDispatchFeature d, Services services) {
        
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
                 ifZero ( isBelow ( ff.modalOperator, services ),
                          longConst ( 200 ) ) } ) );
        
            bindRuleSet ( d, "defOps_jdiv",
               SumFeature.createSum ( new Feature[] {
                 NonDuplicateAppModPositionFeature.INSTANCE,
                 applyTF ( "divNum", tf.polynomial ),
                 applyTF ( "divDenom", tf.polynomial ),
                 applyTF ( "divNum", tf.notContainsDivMod ),
                 applyTF ( "divDenom", tf.notContainsDivMod ),
                 ifZero ( isBelow ( ff.modalOperator, services ),
                          longConst ( 200 ) ) } ) );

            bindRuleSet ( d, "defOps_jdiv_inline",
                          add ( applyTF ( "divNum", tf.literal ),
                                applyTF ( "divDenom", tf.polynomial ),
                                longConst ( -5000 ) ) );
                   
            setupDefOpsExpandMod ( d, services );
            
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

    private void setupDefOpsExpandMod(RuleSetDispatchFeature d, Services services) {
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
                                   ( sub ( or ( tf.addF, tf.mulF ), any () ), services ),
                              not ( subsumedModulus ) ) ) );
        
        bindRuleSet ( d, "defOps_mod",
           ifZero ( add ( applyTF ( "divNum", tf.literal ),
                          applyTF ( "divDenom", tf.literal ) ),
                    longConst ( -4000 ),
                    SumFeature.createSum (
                       applyTF ( "divNum", tf.polynomial ),
                       applyTF ( "divDenom", tf.polynomial ),
		       ifZero ( isBelow ( ff.modalOperator, services ),
				exSubsumedModulus,
				or ( add ( applyTF ( "divNum",
						     tf.notContainsDivMod ),
					   applyTF ( "divDenom",
						     tf.notContainsDivMod ) ),
				     exSubsumedModulus ) ),
		       longConst ( -3500 )
                    ) ) );
    }

    private Feature isBelow(TermFeature t, Services services) {
        final TermBuffer superTerm = new TermBuffer ();
        return not ( sum ( superTerm,
                           SuperTermGenerator.upwards ( any (), services ),
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

    protected Feature setupApprovalF(Proof p_proof) {
        final Feature depSpecF;
        final String depProp
        	= strategyProperties.getProperty(
        		StrategyProperties.DEP_OPTIONS_KEY);
        final SetRuleFilter depFilter = new SetRuleFilter();
        depFilter.addRuleToSet(UseDependencyContractRule.INSTANCE);
        if(depProp.equals(StrategyProperties.DEP_ON)) {
            depSpecF = ConditionalFeature.createConditional(
        	    		depFilter,
        	    		ifZero(new DependencyContractFeature(),
        	    		       longConst(400),
        	    		       inftyConst()));
        } else {
            depSpecF = ConditionalFeature.createConditional(depFilter, 
        	    					    inftyConst());
        }
	
        return add(NonDuplicateAppFeature.INSTANCE, depSpecF);
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
        
        bindRuleSet ( d, "limitObserver",
  	      NonDuplicateAppModPositionFeature.INSTANCE );
        
        bindRuleSet ( d, "partialInvAxiom",
    	      NonDuplicateAppModPositionFeature.INSTANCE );         
        
        setupQuantifierInstantiationApproval ( d );
        setupSplittingApproval ( d );

        bindRuleSet ( d, "apply_select_eq",
              add( isInstantiated("s"),
                   isInstantiated("t1"),
                   or( applyTF( "s", rec( any(), SimplifiedSelectTermFeature.create(heapLDT) ) ),
                       add( NoSelfApplicationFeature.INSTANCE ,
                            applyTF("t1", IsSelectSkolemConstantTermFeature.INSTANCE) ) ) ) );
        bindRuleSet ( d, "apply_auxiliary_eq",
              add( NoSelfApplicationFeature.INSTANCE ,
                   isInstantiated("s"),
                   applyTF("s", rec( any(),
                                     add( SimplifiedSelectTermFeature.create(heapLDT),
                                          not( ff.ifThenElse ) ) ) ),
                   not( ContainsTermFeature.create( instOf("s"),
                                                    instOf("t1") ) ) ) );

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
        setupDefOpsPrimaryCategories ( d, p_proof.getServices() );
        
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

    public static final String JavaCardDLStrategy = "JavaCardDLStrategy";
    
    public Name name () {
        return new Name(JavaCardDLStrategy);
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
//	if(app.rule()==UseDependencyContractRule.INSTANCE/* && (goal.node().serialNr() == 433 || goal.node().serialNr() == 421)*/) {
//	    RuleAppCost result = costComputationF.compute ( app, pio, goal );
//	    System.out.println("Cost for node " + goal.node().serialNr() + ": " + result);
//	    return result;
//	}
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


    public static class Factory implements StrategyFactory {
       /**
        * The unique {@link Name} of this {@link StrategyFactory}.
        */
       public static final Name NAME = new Name(JavaCardDLStrategy);
       
       
       public static final String TOOL_TIP_STOP_AT_DEFAULT = "<html>Stop when (i) the maximum number of rule<br>" +
             "applications is reached or (ii) no more rules are<br>"+
"applicable on the proof tree.</html>";
       public static final String TOOL_TIP_STOP_AT_UNCLOSABLE = "<html>Stop as soon as the first not automatically<br>" +
             "closable goal is encountered.</html>";
       public static final String TOOL_TIP_PROOF_SPLITTING_FREE = "<html>" +
             "Split formulas (if-then-else expressions,<br>" +
             "disjunctions in the antecedent, conjunctions in<br>" +
             "the succedent) freely without restrictions." +
             "</html>";
       public static final String TOOL_TIP_PROOF_SPLITTING_DELAYED = "<html>" +
             "Do not split formulas (if-then-else expressions,<br>" +
             "disjunctions in the antecedent, conjunctions in<br>" +
             "the succedent) as long as programs are present in<br>" +
             "the sequent.<br>" +
             "NB: This does not affect the splitting of formulas<br>" +
             "that themselves contain programs.<br>" +
             "NB2: Delaying splits often prevents KeY from finding<br>" +
             "short proofs, but in some cases it can significantly<br>" +
             "improve the performance." +
             "</html>";
       public static final String TOOL_TIP_PROOF_SPLITTING_OFF = "<html>" +
             "Do never split formulas (if-then-else expressions,<br>" +
             "disjunctions in the antecedent, conjunctions in<br>" +
             "the succedent).<br>" +
             "NB: This does not affect the splitting of formulas<br>" +
             "that contain programs.<br>" +
             "NB2: Without splitting, KeY is often unable to find<br>" +
             "proofs even for simple problems. This option can,<br>" +
             "nevertheless, be meaningful to keep the complexity<br>" +
             "of proofs small and support interactive proving." +
             "</html>";
       public static final String TOOL_TIP_LOOP_INVARIANT = "<html>"+
             "Use loop invariants for loops.<br>"+
             "Three properties have to be shown:<br>"+
             "<ul><li>Validity of invariant of a loop is preserved by the<br>"+
             "loop guard and loop body (initially valid).</li>"+
             "<li>If the invariant was valid at the start of the loop, it holds <br>"+
             "after arbitrarily many loop iterations (body preserves invariant).</li>"+
             "<li>Invariant holds after the loop terminates (use case).</li>"+
             "</ul></html>";
       public static final String TOOL_TIP_LOOP_EXPAND = "<html>"+
             "Unroll loop body."+
             "</html>";
       public static final String TOOL_TIP_LOOP_NONE = "<html>"+
             "Leave loops untouched."+
             "</html>";
       public static final String TOOL_TIP_BLOCK_CONTRACT = "<html>"+
             "If block contracts are specified, Java blocks are replaced by their contract.<br>"+
             "Three properties have to be shown:"+
             "<ul><li>Validity of block contract</li>"+
             "<li>Precondition of contract holds</li>"+
             "<li>Postcondition holds after block terminates</li>"+
             "</ul></html>";
       public static final String TOOL_TIP_BLOCK_EXPAND = "<html>"+
             "Do not use block contracts for Java blocks. Expand Java blocks."+
             "</html>";
       public static final String TOOL_TIP_METHOD_CONTRACT = "<html>Replace method calls by contracts. In some cases<br>" +
             "a method call may also be replaced by its method body.<br>" +
             "If query treatment is activated, this behavior applies<br>" +
             "to queries as well.</html>";
       public static final String TOOL_TIP_METHOD_EXPAND = "<html>Replace method calls by their bodies, i.e. by their<br>" +
             "implementation. Method contracts are strictly deactivated.</html>";
       public static final String TOOL_TIP_METHOD_NONE = "<html>" +
             "Stop when encountering a method" +
             "</html>";
       public static final String TOOL_TIP_CLASSAXIOM_FREE =
           "<html>Expand class axioms (such as invariants) freely.</html>";
       public static final String TOOL_TIP_CLASSAXIOM_DELAYED =
           "<html>Expand class axioms (such as invariants) only after symbolic execution.</html>";
       public static final String TOOL_TIP_CLASSAXIOM_OFF =
           "<html>Do not expand class axioms (such as invariants).</html>";
       public static final String TOOL_TIP_DEPENDENCY_ON = "<html>Uses the information in JML's <tt>accessible</tt> clauses<br>" +
             "in order to simplify heap terms. For instance, consider the term<br>" +
             "<center><i>f(store(heap,o,a,1))</i></center>" +
             "If <i>f</i> does not depend on the location <i>(o,a)</i>, which is<br>" +
             "expressed by an <tt>accessible</tt> clause, then the term can be <br>" +
             "simplified to <i>f(heap)</i>.</html>";
       public static final String TOOL_TIP_DEPENDENCY_OFF = "<html>Does <i>not</i> use the framing information contained in JML's <br>" +
             "<tt>accessible</tt> clauses automatically in order to simplify heap terms.<br>" +
 "This prevents the automatic proof search to find proofs for a number of problems.<br>" +
 "On the other hand, the automatic proof search does not use a particular order in<br>" +
             "which <tt>accessible</tt> clauses are used. Since the usage of an <tt>accessible</tt><br>" +
             "clause is splitting, this might result in huge (or even infeasible) proofs.</html>";
       public static final String TOOL_TIP_QUERY_ON = "<html>Rewrite query to a method call so that contracts or inlining<br>" +
             "can be used. A query is a method that is used as a function <br>" +
             "in the logic and stems from the specification.<br><br>" +
             "Whether contracts or inlining are used depends on the <br>" +
             "Method Treatment settings.</html>";
       public static final String TOOL_TIP_QUERY_RESTRICTED = "<html>Rewrite query to a method call (expanded) so that contracts or inlining can be used.<br>" +
             "<ul><li> Priority of expanding queries occuring earlier on a branch is higher than<br>" +
         " for queries introduced more recently. This approximates in a breath-first search<br>" +
             " with respect to query expansion.</li>" +
         "<li> Reexpansion of identical query terms is suppressed.</li>" +
         "<li> A query is not expanded if one of its arguments contains a literal greater<br>" +
         " than "+QueryExpandCost.ConsideredAsBigLiteral+", or smaller than "+(-QueryExpandCost.ConsideredAsBigLiteral)+". This helps detecting loops in a proof.</li>" +
         "<li> Queries are expanded after the loop body in the \"Preserves Invariant\"<br>" +
         " branch of the loop invariant rule.</li>" +
         "<li> Queries are expanded in the Base Case and the conclusio of the Step Case <br>" +
         " branch when using Auto Induction.</li>" +
         "</ul></html>";
       public static final String TOOL_TIP_QUERY_OFF = "<html>"+
             "Turn rewriting of query off."+
            "</html>";
       public static final String TOOL_TIP_EXPAND_LOCAL_QUERIES_ON = "<html>Replaces queries by their method body in certain safe cases.<br>" + 
             "Safe cases are:"+
             "<ul><li>the return type of the expanded method is known</li>"+
            "<li>the object on which the methodcall is invoked, is self or a parent of self</li></ul>"+
"This mechanism works independently of the query treatment <br>" +
            "and method treatment settings above.<br>" +
            "<i>The internal rule name is Query Axiom</i></html>";
       public static final String TOOL_TIP_EXPAND_LOCAL_QUERIES_OFF = "<html>"+
             "Expansion of local queries is turned off. <br>"+
  "This setting is independent of the query treatment setting."+
 "</html>";
       public static final String TOOL_TIP_ARITHMETIC_BASE = "<html>" +
             "Basic arithmetic support:" +
             "<ul>" +
             "<li>Simplification of polynomial expressions</li>" +
             "<li>Computation of Gr&ouml;bner Bases for polynomials in the antecedent</li>" +
             "<li>(Partial) Omega procedure for handling linear inequations</li>" +
             "</ul>" +
             "</html>";
       public static final String TOOL_TIP_ARITHMETIC_DEF_OPS = "<html>" +
             "Automatically expand defined symbols like:" +
             "<ul>" +
             "<li><tt>/</tt>, <tt>%</tt>, <tt>jdiv</tt>, <tt>jmod</tt>, ...</li>" +
             "<li><tt>int_RANGE</tt>, <tt>short_MIN</tt>, ...</li>" +
             "<li><tt>inInt</tt>, <tt>inByte</tt>, ...</li>" +
             "<li><tt>addJint</tt>, <tt>mulJshort</tt>, ...</li>" +
             "</ul>" +
             "</html>";
       public static final String TOOL_TIP_ARITHMETIC_MODEL_SEARCH = "<html>" +
             "Support for non-linear inequations and model search.<br>" +
             "In addition, this performs:" +
             "<ul>" +
             "<li>Multiplication of inequations with each other</li>" +
             "<li>Systematic case distinctions (cuts)</li>" +
             "</ul>" +
             "This method is guaranteed to find counterexamples for<br>" +
             "invalid goals that only contain polynomial (in)equations.<br>" +
             "Such counterexamples turn up as trivially unprovable goals.<br>" +
             "It is also able to prove many more valid goals involving<br>" +
             "(in)equations, but will in general not terminate on such goals." +
             "</html>";
       public static final String TOOL_TIP_QUANTIFIER_NONE = "<html>" +
             "Do not instantiate quantified formulas automatically" +
             "</html>";
       public static final String TOOL_TIP_QUANTIFIER_NO_SPLITS = "<html>" +
             "Instantiate quantified formulas automatically<br>" +
             "with terms that occur in a sequent, but only if<br>" +
             "this does not cause proof splitting. Further, quantified<br>" +
             "formulas that contain queries are not instantiated<br>" +
             "automatically." +
             "</html>";
       public static final String TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS = "<html>" +
             "Instantiate quantified formulas automatically<br>" +
             "with terms that occur in a sequent, but if the<br>" +
             "sequent contains programs then only perform<br>" +
             "instantiations that do not cause proof splitting.<br>" +
             "Further, quantified formulas that contain queries<br>" +
             "are not instantiated automatically." +
             "</html>";
       public static final String TOOL_TIP_QUANTIFIER_FREE = "<html>" +
             "Instantiate quantified formulas automatically<br>" +
             "with terms that occur in a sequent, also if this<br>" +
             "might cause proof splitting." +
             "</html>";
       public static final String TOOL_TIP_AUTO_INDUCTION_ON = "<html>" +
             "Create an inductive proof for formulas of the form:<br>" +
             "      ==>  \\forall int i; 0&lt;=i->phi <br>" +
             "and certain other forms. The induction hypothesis<br>" +
             "is the subformula phi. The rule is applied before<br>" +
             "beta rules are applied.<br>" +
             "<br>" +
             "When encountering a formula of the form<br>" +
             "      ==>  (\\forall int i; 0&lt;=i->phi) & psi <br>" +
             "and certain similar forms, then the quantified formula<br>" +
             "is used in the Use Case branch as a lemma for psi,<br>" +
             "i.e., the sequent in the Use Case has the form:<br>" +
             "      (\\forall int i; 0&lt;=i->phi) ==>  psi <br>" +
             "</html>";
       public static final String TOOL_TIP_AUTO_INDUCTION_RESTRICTED = "<html>" +
             "Performs auto induction only on quantified formulas that<br>" +
             "(a) fullfill a certain pattern (as described for the \"on\"option)<br>" +
             "and (b) whose quantified variable has the suffix \"Ind\" or \"IND\".<br>" +
             "For instance, auto induction will be applied on:<br>" +
                "      ==>  \\forall int iIND; 0&lt;=iIND->phi <br>" +
                "but not on: <br>" +
                "      ==>  \\forall int i; 0&lt;=i->phi <br>" +
                "</html>";
       public static final String TOOL_TIP_AUTO_INDUCTION_OFF = "<html>" +
             "Deactivates automatic creation of inductive proofs.<br>" +
             "In order to make use of auto induction, activate <br>" +
             "auto induction early in proofs before the <br>" +
             "quantified formula that is to be proven inductively<br>" +
             "is Skolemized (using the delta rule). Auto induction<br>" +
             "is not applied on Skolemized formulas in order to<br>" +
             "limit the number of inductive proofs." +
             "</html>";
       public static String TOOL_TIP_USER_OFF(int i) {return "Taclets of the rule set \"userTaclets" + i 
             + "\" are not applied automatically";}

        public static String TOOL_TIP_USER_LOW(int i) {return "Taclets of the rule set \"userTaclets" + i
             + "\" are applied automatically with low priority";}

        public static String TOOL_TIP_USER_HIGH(int i) {return "Taclets of the rule set \"userTaclets" + i
             + "\" are applied automatically with high priority";}

        public Factory () {
        }

        public Strategy create ( Proof p_proof, 
                StrategyProperties strategyProperties) {     
            return new JavaCardDLStrategy ( p_proof, strategyProperties );
        }
        
        public Name name () {
            return NAME;
        }

        @Override
        public StrategySettingsDefinition getSettingsDefinition() {
           // Properties
           OneOfStrategyPropertyDefinition stopAt = new OneOfStrategyPropertyDefinition(StrategyProperties.STOPMODE_OPTIONS_KEY, 
                 "Stop at", 
                 new StrategyPropertyValueDefinition(StrategyProperties.STOPMODE_DEFAULT, "Default", TOOL_TIP_STOP_AT_DEFAULT),
                 new StrategyPropertyValueDefinition(StrategyProperties.STOPMODE_NONCLOSE, "Unclosable", TOOL_TIP_STOP_AT_UNCLOSABLE));
           OneOfStrategyPropertyDefinition proofSplitting = new OneOfStrategyPropertyDefinition(StrategyProperties.SPLITTING_OPTIONS_KEY, 
                 "Proof splitting",
                 new StrategyPropertyValueDefinition(StrategyProperties.SPLITTING_NORMAL, "Free", TOOL_TIP_PROOF_SPLITTING_FREE),
                 new StrategyPropertyValueDefinition(StrategyProperties.SPLITTING_DELAYED, "Delayed", TOOL_TIP_PROOF_SPLITTING_DELAYED),
                 new StrategyPropertyValueDefinition(StrategyProperties.SPLITTING_OFF, "Off", TOOL_TIP_PROOF_SPLITTING_OFF));
           OneOfStrategyPropertyDefinition loopTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.LOOP_OPTIONS_KEY, 
                 "Loop treatment",
                 new StrategyPropertyValueDefinition(StrategyProperties.LOOP_INVARIANT, "Invariant", TOOL_TIP_LOOP_INVARIANT),
                 new StrategyPropertyValueDefinition(StrategyProperties.LOOP_EXPAND, "Expand", TOOL_TIP_LOOP_EXPAND),
                 new StrategyPropertyValueDefinition(StrategyProperties.LOOP_NONE, "None", TOOL_TIP_LOOP_NONE));
           OneOfStrategyPropertyDefinition blockTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.BLOCK_OPTIONS_KEY, 
                 "Block treatment",
                 new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_CONTRACT, "Contract", TOOL_TIP_BLOCK_CONTRACT),
                 new StrategyPropertyValueDefinition(StrategyProperties.BLOCK_EXPAND, "Expand", TOOL_TIP_BLOCK_EXPAND));
           OneOfStrategyPropertyDefinition methodTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.METHOD_OPTIONS_KEY,
                 "Method treatment",
                 new StrategyPropertyValueDefinition(StrategyProperties.METHOD_CONTRACT, "Contract", TOOL_TIP_METHOD_CONTRACT),
                 new StrategyPropertyValueDefinition(StrategyProperties.METHOD_EXPAND, "Expand", TOOL_TIP_METHOD_EXPAND),
                 new StrategyPropertyValueDefinition(StrategyProperties.METHOD_NONE, "None", TOOL_TIP_METHOD_NONE));
           OneOfStrategyPropertyDefinition dependencyContracts = new OneOfStrategyPropertyDefinition(StrategyProperties.DEP_OPTIONS_KEY, 
                 "Dependency contracts",
                 new StrategyPropertyValueDefinition(StrategyProperties.DEP_ON, "On", TOOL_TIP_DEPENDENCY_ON),
                 new StrategyPropertyValueDefinition(StrategyProperties.DEP_OFF, "Off", TOOL_TIP_DEPENDENCY_OFF));
           OneOfStrategyPropertyDefinition expandLocalQueries = new OneOfStrategyPropertyDefinition(StrategyProperties.QUERYAXIOM_OPTIONS_KEY, 
                 "Expand local queries:",
                 new StrategyPropertyValueDefinition(StrategyProperties.QUERYAXIOM_ON, "On", TOOL_TIP_EXPAND_LOCAL_QUERIES_ON),
                 new StrategyPropertyValueDefinition(StrategyProperties.QUERYAXIOM_OFF, "Off", TOOL_TIP_EXPAND_LOCAL_QUERIES_OFF));
           OneOfStrategyPropertyDefinition queryTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.QUERY_OPTIONS_KEY, 
                 "Query treatment",
                 new AbstractStrategyPropertyDefinition[] {expandLocalQueries},
                 new StrategyPropertyValueDefinition(StrategyProperties.QUERY_ON, "On", TOOL_TIP_QUERY_ON),
                 new StrategyPropertyValueDefinition(StrategyProperties.QUERY_RESTRICTED, "Restricted", TOOL_TIP_QUERY_RESTRICTED),
                 new StrategyPropertyValueDefinition(StrategyProperties.QUERY_OFF, "Off", TOOL_TIP_QUERY_OFF));
           OneOfStrategyPropertyDefinition arithmeticTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY, 
                 "Arithmetic treatment",
                 new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_NONE, "Basic", TOOL_TIP_ARITHMETIC_BASE),
                 new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_DEF_OPS, "DefOps", TOOL_TIP_ARITHMETIC_DEF_OPS),
                 new StrategyPropertyValueDefinition(StrategyProperties.NON_LIN_ARITH_COMPLETION, "Model Search", TOOL_TIP_ARITHMETIC_MODEL_SEARCH));
           OneOfStrategyPropertyDefinition quantifierTreatment = new OneOfStrategyPropertyDefinition(StrategyProperties.QUANTIFIERS_OPTIONS_KEY, 
                 "Quantifier treatment",
                 2,
                 new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NONE, "None", TOOL_TIP_QUANTIFIER_NONE, 2, 4),
                 new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NON_SPLITTING, "No Splits", TOOL_TIP_QUANTIFIER_NO_SPLITS, 6, 2),
                 new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS, "No Splits with Progs", TOOL_TIP_QUANTIFIER_NO_SPLITS_WITH_PROGS, 2, 4),
                 new StrategyPropertyValueDefinition(StrategyProperties.QUANTIFIERS_INSTANTIATE, "Free", TOOL_TIP_QUANTIFIER_FREE, 6, 2));
           OneOfStrategyPropertyDefinition classAxiom = new OneOfStrategyPropertyDefinition(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY, 
                 "Class axiom rule",
                 new StrategyPropertyValueDefinition(StrategyProperties.CLASS_AXIOM_FREE, "Free", TOOL_TIP_CLASSAXIOM_FREE),
                 new StrategyPropertyValueDefinition(StrategyProperties.CLASS_AXIOM_DELAYED, "Delayed", TOOL_TIP_CLASSAXIOM_DELAYED),
                 new StrategyPropertyValueDefinition(StrategyProperties.CLASS_AXIOM_OFF, "Off", TOOL_TIP_CLASSAXIOM_OFF));
           OneOfStrategyPropertyDefinition autoInduction = new OneOfStrategyPropertyDefinition(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY, 
                 "Auto Induction",
                 new StrategyPropertyValueDefinition(StrategyProperties.AUTO_INDUCTION_LEMMA_ON, "On", TOOL_TIP_AUTO_INDUCTION_ON),
                 new StrategyPropertyValueDefinition(StrategyProperties.AUTO_INDUCTION_RESTRICTED, "Restricted", TOOL_TIP_AUTO_INDUCTION_RESTRICTED),
                 new StrategyPropertyValueDefinition(StrategyProperties.AUTO_INDUCTION_OFF, "Off", TOOL_TIP_AUTO_INDUCTION_OFF));
           // User properties
           List<AbstractStrategyPropertyDefinition> props = new LinkedList<AbstractStrategyPropertyDefinition>();
           for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
              OneOfStrategyPropertyDefinition user = new OneOfStrategyPropertyDefinition(StrategyProperties.USER_TACLETS_OPTIONS_KEY(i), 
                    i + ":  ",
                    new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_OFF, "Off", TOOL_TIP_USER_OFF(i), 3, 1),
                    new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_LOW, "Low prior.", TOOL_TIP_USER_LOW(i), 4, 2),
                    new StrategyPropertyValueDefinition(StrategyProperties.USER_TACLETS_HIGH, "High prior.", TOOL_TIP_USER_HIGH(i), 6, 2));
              props.add(user);
           }
           OneOfStrategyPropertyDefinition userOptions = new OneOfStrategyPropertyDefinition(null, 
                 "User-specific taclet sets",
                 "<html>" +
                 "These options define whether user- and problem-specific taclet sets<br>" +
                 "are applied automatically by the strategy. Problem-specific taclets<br>" +
                 "can be defined in the \\rules-section of a .key-problem file. For<br>" +
                 "automatic application, the taclets have to contain a clause<br>" +
                 "\\heuristics(userTaclets1), \\heuristics(userTaclets2), etc." +
                 "</html>",
                 -1,
                 props.toArray(new AbstractStrategyPropertyDefinition[props.size()]));
           // Model
           return new StrategySettingsDefinition("Java DL Options", 
                                                 stopAt,
                                                 proofSplitting,
                                                 loopTreatment,
                                                 blockTreatment,
                                                 methodTreatment,
                                                 dependencyContracts,
                                                 queryTreatment,
                                                 arithmeticTreatment,
                                                 quantifierTreatment,
                                                 classAxiom,
                                                 autoInduction,
                                                 userOptions );
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
    private final ValueTermFeature vf;
    
    private class ArithTermFeatures {

	public ArithTermFeatures (IntegerLDT numbers){
            Z = numbers.getNumberSymbol ();
            C = numbers.getCharSymbol();
            
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
            
            
            charLiteral = op ( C );

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
        final Function C;
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

        final TermFeature charLiteral;

        
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
            notExecutable = not ( program );
            
            notContainsExecutable = not ( ContainsExecutableCodeTermFeature.PROGRAMS );
            
            cutAllowed =
                add ( notContainsExecutable,
                      tf.notContainsProduct,
                      or ( tf.eqF,
                           OperatorClassTF.create ( Function.class ),
                           OperatorClassTF.create ( ParsableVariable.class )) ); //XXX
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

    private class ValueTermFeature {

        public ValueTermFeature() {
            equals = op(Equality.EQUALS);
            tt = op(Junctor.TRUE);
            ff = op(Junctor.FALSE);
            nullTerm = op(heapLDT.getNull());
        }

        final TermFeature equals;
        final TermFeature tt;
        final TermFeature ff;
        final TermFeature nullTerm;
    }
}
