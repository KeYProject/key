/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.BooleanLDT;
import de.uka.ilkd.key.ldt.CharListLDT;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesSmallerThanFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EliminableQuantifierTF;
import de.uka.ilkd.key.strategy.quantifierHeuristics.HeuristicInstantiation;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCost;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCostScalerFeature;
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
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termfeature.IsInductionVariable;
import de.uka.ilkd.key.strategy.termfeature.IsNonRigidTermFeature;
import de.uka.ilkd.key.strategy.termfeature.IsSelectSkolemConstantTermFeature;
import de.uka.ilkd.key.strategy.termfeature.OperatorClassTF;
import de.uka.ilkd.key.strategy.termfeature.PrimitiveHeapTermFeature;
import de.uka.ilkd.key.strategy.termfeature.SimplifiedSelectTermFeature;
import de.uka.ilkd.key.strategy.termfeature.TermFeature;
import de.uka.ilkd.key.strategy.termgenerator.AllowedCutPositionsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.HeapGenerator;
import de.uka.ilkd.key.strategy.termgenerator.MultiplesModEquationsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.RootsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SequentFormulasGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SubtermGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;
import de.uka.ilkd.key.strategy.termgenerator.TriggeredInstantiations;
import de.uka.ilkd.key.util.MiscTools;

/**
 * Strategy tailored to be used as long as a java program can be found in the sequent.
 */
public class JavaCardDLStrategy extends AbstractFeatureStrategy {
    public static final AtomicLong PERF_COMPUTE = new AtomicLong();
    public static final AtomicLong PERF_APPROVE = new AtomicLong();
    public static final AtomicLong PERF_INSTANTIATE = new AtomicLong();

    public static final String JAVA_CARD_DL_STRATEGY = "JavaCardDLStrategy";

    private static final int IN_EQ_SIMP_NON_LIN_COST = 1000;
    private static final int POLY_DIVISION_COST = -2250;

    protected final StrategyProperties strategyProperties;

    private final RuleSetDispatchFeature costComputationDispatcher;
    private final Feature costComputationF;
    private final RuleSetDispatchFeature approvalDispatcher;
    private final Feature approvalF;
    private final RuleSetDispatchFeature instantiationDispatcher;
    private final Feature instantiationF;

    private final HeapLDT heapLDT;

    private final ArithTermFeatures tf;
    private final FormulaTermFeatures ff;
    private final ValueTermFeature vf;


    protected JavaCardDLStrategy(Proof proof, StrategyProperties strategyProperties) {

        super(proof);
        heapLDT = getServices().getTypeConverter().getHeapLDT();

        this.strategyProperties = (StrategyProperties) strategyProperties.clone();

        this.tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        this.ff = new FormulaTermFeatures(this.tf);
        this.vf = new ValueTermFeature(op(heapLDT.getNull()));

        costComputationDispatcher = setupCostComputationF();
        approvalDispatcher = setupApprovalDispatcher();
        instantiationDispatcher = setupInstantiationF();

        costComputationF = setupGlobalF(costComputationDispatcher);
        instantiationF = setupGlobalF(instantiationDispatcher);
        approvalF = add(setupApprovalF(), approvalDispatcher);

    }

    protected final RuleSetDispatchFeature getCostComputationDispatcher() {
        return costComputationDispatcher;
    }

    protected final RuleSetDispatchFeature getInstantiationDispatcher() {
        return instantiationDispatcher;
    }

    protected Feature setupGlobalF(Feature dispatcher) {
        final Feature ifMatchedF = ifZero(MatchedIfFeature.INSTANCE, longConst(+1));

        final Feature methodSpecF;
        final String methProp =
            strategyProperties.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);
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

        final String queryProp =
            strategyProperties.getProperty(StrategyProperties.QUERY_OPTIONS_KEY);
        final Feature queryF;
        if (queryProp.equals(StrategyProperties.QUERY_ON)) {
            queryF = querySpecFeature(new QueryExpandCost(200, 1, 1, false));
        } else if (queryProp.equals(StrategyProperties.QUERY_RESTRICTED)) {
            // All tests in the example directory pass with this strategy.
            // Hence, the old query_on strategy is obsolete.
            queryF = querySpecFeature(new QueryExpandCost(500, 0, 1, true));
        } else if (queryProp.equals(StrategyProperties.QUERY_OFF)) {
            queryF = querySpecFeature(inftyConst());
        } else {
            queryF = null;
            assert false;
        }

        final Feature depSpecF;
        final String depProp = strategyProperties.getProperty(StrategyProperties.DEP_OPTIONS_KEY);
        final SetRuleFilter depFilter = new SetRuleFilter();
        depFilter.addRuleToSet(UseDependencyContractRule.INSTANCE);
        if (depProp.equals(StrategyProperties.DEP_ON)) {
            depSpecF = ConditionalFeature.createConditional(depFilter, longConst(250));
        } else {
            depSpecF = ConditionalFeature.createConditional(depFilter, inftyConst());
        }

        // NOTE (DS, 2019-04-10): The new loop-scope based rules are realized
        // as taclets. The strategy settings for those are handled further
        // down in this class.
        Feature loopInvF;
        final String loopProp = strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY);
        if (loopProp.equals(StrategyProperties.LOOP_INVARIANT)) {
            loopInvF = loopInvFeature(longConst(0));
            /*
             * NOTE (DS, 2019-04-10): Deactivated the built-in loop scope rule since we now have the
             * loop scope taclets which are based on the same theory, but offer several advantages.
             */
            // } else if (loopProp.equals(StrategyProperties.LOOP_SCOPE_INVARIANT)) {
            // loopInvF = loopInvFeature(inftyConst(), longConst(0));
        } else {
            loopInvF = loopInvFeature(inftyConst());
        }

        final Feature blockFeature;
        final Feature loopBlockFeature;
        final Feature loopBlockApplyHeadFeature;
        final String blockProperty =
            strategyProperties.getProperty(StrategyProperties.BLOCK_OPTIONS_KEY);
        if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT_INTERNAL)) {
            blockFeature = blockContractInternalFeature(longConst(Long.MIN_VALUE));
            loopBlockFeature = loopContractInternalFeature(longConst(Long.MIN_VALUE));
            loopBlockApplyHeadFeature = loopContractApplyHead(longConst(Long.MIN_VALUE));
        } else if (blockProperty.equals(StrategyProperties.BLOCK_CONTRACT_EXTERNAL)) {
            blockFeature = blockContractExternalFeature(longConst(Long.MIN_VALUE));
            loopBlockFeature =
                SumFeature.createSum(loopContractExternalFeature(longConst(Long.MIN_VALUE)),
                    loopContractInternalFeature(longConst(42)));
            loopBlockApplyHeadFeature = loopContractApplyHead(longConst(Long.MIN_VALUE));
        } else {
            blockFeature = blockContractInternalFeature(inftyConst());
            loopBlockFeature = loopContractExternalFeature(inftyConst());
            loopBlockApplyHeadFeature = loopContractApplyHead(inftyConst());
        }

        final Feature oneStepSimplificationF = oneStepSimplificationFeature(longConst(-11000));

        final Feature mergeRuleF;
        final String mpsProperty =
            strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);
        if (mpsProperty.equals(StrategyProperties.MPS_MERGE)) {
            mergeRuleF = mergeRuleFeature(longConst(-4000));
        } else {
            mergeRuleF = mergeRuleFeature(inftyConst());
        }

        // final Feature smtF = smtFeature(inftyConst());

        return SumFeature.createSum(AutomatedRuleFeature.INSTANCE, NonDuplicateAppFeature.INSTANCE,
            // splitF,
            // strengthenConstraints,
            AgeFeature.INSTANCE, oneStepSimplificationF, mergeRuleF,
            // smtF,
            methodSpecF, queryF, depSpecF, loopInvF, blockFeature, loopBlockFeature,
            loopBlockApplyHeadFeature, ifMatchedF, dispatcher);
    }

    private Feature oneStepSimplificationFeature(Feature cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(MiscTools.findOneStepSimplifier(getProof()));
        return ConditionalFeature.createConditional(filter, cost);
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the computation of costs for taclet
    // applications
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private RuleSetDispatchFeature setupCostComputationF() {
        final IntegerLDT numbers = getServices().getTypeConverter().getIntegerLDT();
        final LocSetLDT locSetLDT = getServices().getTypeConverter().getLocSetLDT();

        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "semantics_blasting", inftyConst());
        bindRuleSet(d, "simplify_heap_high_costs", inftyConst());

        bindRuleSet(d, "closure", -15000);
        bindRuleSet(d, "alpha", -7000);
        bindRuleSet(d, "delta", -6000);
        bindRuleSet(d, "simplify_boolean", -200);

        bindRuleSet(d, "concrete",
            add(longConst(-11000), ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 10.0)));
        bindRuleSet(d, "simplify", -4500);
        bindRuleSet(d, "simplify_enlarging", -2000);
        bindRuleSet(d, "simplify_ENLARGING", -1900);
        bindRuleSet(d, "simplify_expression", -100);
        bindRuleSet(d, "executeIntegerAssignment", -100);
        bindRuleSet(d, "executeDoubleAssignment", -100);
        bindRuleSet(d, "simplify_int", inftyConst());

        bindRuleSet(d, "javaIntegerSemantics",
            ifZero(sequentContainsNoPrograms(), longConst(-5000), ifZero(
                leq(CountBranchFeature.INSTANCE, longConst(1)), longConst(-5000), inftyConst())));

        // always give infinite cost to obsolete rules
        bindRuleSet(d, "obsolete", inftyConst());

        // taclets for special invariant handling
        bindRuleSet(d, "loopInvariant", -20000);

        setupSelectSimplification(d);

        bindRuleSet(d, "no_self_application",
            ifZero(MatchedIfFeature.INSTANCE, NoSelfApplicationFeature.INSTANCE));

        bindRuleSet(d, "find_term_not_in_assumes", ifZero(MatchedIfFeature.INSTANCE,
            not(contains(AssumptionProjection.create(0), FocusProjection.INSTANCE))));

        bindRuleSet(d, "update_elim",
            add(longConst(-8000), ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 10.0)));
        bindRuleSet(d, "update_apply_on_update",
            add(longConst(-7000), ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 10.0)));
        bindRuleSet(d, "update_join", -4600);
        bindRuleSet(d, "update_apply", -4500);

        setUpStringNormalisation(d);

        setupSplitting(d);

        bindRuleSet(d, "test_gen", inftyConst());
        bindRuleSet(d, "test_gen_empty_modality_hide", inftyConst());
        bindRuleSet(d, "test_gen_quan", inftyConst());
        bindRuleSet(d, "test_gen_quan_num", inftyConst());

        bindRuleSet(d, "gamma", add(not(isInstantiated("t")),
            ifZero(allowQuantifierSplitting(), longConst(0), longConst(50))));
        bindRuleSet(d, "gamma_destructive", inftyConst());

        bindRuleSet(d, "triggered", add(not(isTriggerVariableInstantiated()), longConst(500)));

        bindRuleSet(d, "comprehension_split",
            add(applyTF(FocusFormulaProjection.INSTANCE, ff.notContainsExecutable),
                ifZero(allowQuantifierSplitting(), longConst(2500), longConst(5000))));

        setupReplaceKnown(d);

        bindRuleSet(d, "confluence_restricted",
            ifZero(MatchedIfFeature.INSTANCE, DiffFindAndIfFeature.INSTANCE));

        setupApplyEq(d, numbers);

        bindRuleSet(d, "insert_eq_nonrigid",
            applyTF(FocusProjection.create(0), IsNonRigidTermFeature.INSTANCE));

        bindRuleSet(d, "order_terms",
            add(ifZero(applyTF("commEqLeft", tf.intF),
                add(applyTF("commEqRight", tf.monomial), applyTF("commEqLeft", tf.polynomial),
                    monSmallerThan("commEqLeft", "commEqRight", numbers)),
                termSmallerThan("commEqLeft", "commEqRight")), longConst(-5000)));

        bindRuleSet(d, "simplify_literals",
            // ifZero ( ConstraintStrengthenFeatureUC.create(proof),
            // longConst ( 0 ),
            longConst(-8000));

        bindRuleSet(d, "nonDuplicateAppCheckEq", EqNonDuplicateAppFeature.INSTANCE);

        bindRuleSet(d, "simplify_instanceof_static",
            add(EqNonDuplicateAppFeature.INSTANCE, longConst(-500)));

        bindRuleSet(d, "comprehensions",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-50)));

        bindRuleSet(d, "comprehensions_high_costs",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(10000)));

        bindRuleSet(d, "comprehensions_low_costs",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-5000)));

        bindRuleSet(d, "evaluate_instanceof", longConst(-500));

        bindRuleSet(d, "instanceof_to_exists", TopLevelFindFeature.ANTEC);

        bindRuleSet(d, "try_apply_subst",
            add(EqNonDuplicateAppFeature.INSTANCE, longConst(-10000)));

        final TermBuffer superFor = new TermBuffer();
        bindRuleSet(d, "split_if",
            add(sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                applyTF(superFor, not(ff.program))), longConst(50)));

        final String[] exceptionsWithPenalty = new String[] { "java.lang.NullPointerException",
            "java.lang.ArrayIndexOutOfBoundsException", "java.lang.ArrayStoreException",
            "java.lang.ClassCastException" };

        bindRuleSet(d, "simplify_prog",
            ifZero(ThrownExceptionFeature.create(exceptionsWithPenalty, getServices()),
                longConst(500),
                ifZero(isBelow(add(ff.forF, not(ff.atom))), longConst(200), longConst(-100))));

        bindRuleSet(d, "simplify_prog_subset", longConst(-4000));
        bindRuleSet(d, "modal_tautology", longConst(-10000));

        // features influenced by the strategy options

        boolean useLoopExpand = strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY)
                .equals(StrategyProperties.LOOP_EXPAND);
        boolean useLoopInvTaclets =
            strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY)
                    .equals(StrategyProperties.LOOP_SCOPE_INV_TACLET);
        boolean useLoopScopeExpand =
            strategyProperties.getProperty(StrategyProperties.LOOP_OPTIONS_KEY)
                    .equals(StrategyProperties.LOOP_SCOPE_EXPAND);
        /*
         * boolean useBlockExpand = strategyProperties.getProperty(
         * StrategyProperties.BLOCK_OPTIONS_KEY). equals(StrategyProperties.BLOCK_EXPAND);
         */
        boolean programsToRight = true; // XXX

        final String methProp =
            strategyProperties.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);

        switch (methProp) {
        case StrategyProperties.METHOD_CONTRACT:
            /*
             * If method treatment by contracts is chosen, this does not mean that method expansion
             * is disabled. The original cost was 200 and is now increased to 2000 in order to
             * repress method expansion stronger when method treatment by contracts is chosen.
             */
            bindRuleSet(d, "method_expand", longConst(2000));
            break;
        case StrategyProperties.METHOD_EXPAND:
            bindRuleSet(d, "method_expand", longConst(100));
            break;
        case StrategyProperties.METHOD_NONE:
            bindRuleSet(d, "method_expand", inftyConst());
            break;
        default:
            throw new RuntimeException("Unexpected strategy property " + methProp);
        }

        final String mpsProp = strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);

        switch (mpsProp) {
        case StrategyProperties.MPS_MERGE:
            /*
             * For this case, we use a special feature, since deleting merge points should only be
             * done after a merge rule application.
             */
            bindRuleSet(d, "merge_point", DeleteMergePointRuleFeature.INSTANCE);
            break;
        case StrategyProperties.MPS_SKIP:
            bindRuleSet(d, "merge_point", longConst(-5000));
            break;
        case StrategyProperties.MPS_NONE:
            bindRuleSet(d, "merge_point", inftyConst());
            break;
        default:
            throw new RuntimeException("Unexpected strategy property " + methProp);
        }


        final String queryAxProp =
            strategyProperties.getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
        switch (queryAxProp) {
        case StrategyProperties.QUERYAXIOM_ON:
            bindRuleSet(d, "query_axiom", longConst(-3000));
            break;
        case StrategyProperties.QUERYAXIOM_OFF:
            bindRuleSet(d, "query_axiom", inftyConst());
            break;
        default:
            throw new RuntimeException("Unexpected strategy property " + queryAxProp);
        }

        if (classAxiomApplicationEnabled()) {
            bindRuleSet(d, "classAxiom", longConst(-250));
        } else {
            bindRuleSet(d, "classAxiom", inftyConst());
        }

        bindRuleSet(d, "loop_expand", useLoopExpand ? longConst(0) : inftyConst());
        bindRuleSet(d, "loop_scope_inv_taclet", useLoopInvTaclets ? longConst(0) : inftyConst());
        bindRuleSet(d, "loop_scope_expand", useLoopScopeExpand ? longConst(1000) : inftyConst());

        /*
         * bindRuleSet ( d, "block_expand", useBlockExpand ? longConst ( 0 ) : inftyConst () );
         */

        // delete cast
        bindRuleSet(d, "cast_deletion",
            ifZero(implicitCastNecessary(instOf("castedTerm")), longConst(-5000), inftyConst()));

        bindRuleSet(d, "type_hierarchy_def", -6500);

        // partial inv axiom
        bindRuleSet(d, "partialInvAxiom",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(10000)));

        // inReachableState
        bindRuleSet(d, "inReachableStateImplication",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(100)));

        // limit observer (must have better priority than "classAxiom")
        bindRuleSet(d, "limitObserver",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-200)));

        if (programsToRight) {
            bindRuleSet(d, "boxDiamondConv",
                SumFeature.createSum(
                    new FindPrefixRestrictionFeature(
                        FindPrefixRestrictionFeature.PositionModifier.ALLOW_UPDATE_AS_PARENT,
                        FindPrefixRestrictionFeature.PrefixChecker.ANTEC_POLARITY),
                    longConst(-1000)));
        } else {
            bindRuleSet(d, "boxDiamondConv", inftyConst());
        }

        bindRuleSet(d, "cut", not(isInstantiated("cutFormula")));

        setupUserTaclets(d);

        setupArithPrimaryCategories(d);
        setupPolySimp(d, numbers);
        setupInEqSimp(d, numbers);

        setupDefOpsPrimaryCategories(d);

        setupSystemInvariantSimp(d);

        if (quantifierInstantiatedEnabled()) {
            setupFormulaNormalisation(d, numbers, locSetLDT);
        } else {
            bindRuleSet(d, "negationNormalForm", inftyConst());
            bindRuleSet(d, "moveQuantToLeft", inftyConst());
            bindRuleSet(d, "conjNormalForm", inftyConst());
            bindRuleSet(d, "apply_equations_andOr", inftyConst());
            bindRuleSet(d, "elimQuantifier", inftyConst());
            bindRuleSet(d, "distrQuantifier", inftyConst());
            bindRuleSet(d, "swapQuantifiers", inftyConst());
            bindRuleSet(d, "pullOutQuantifierAll", inftyConst());
            bindRuleSet(d, "pullOutQuantifierEx", inftyConst());
        }

        // For taclets that need instantiation, but where the instantiation is
        // deterministic and does not have to be repeated at a later point, we
        // setup the same feature terms as in the instantiation method. The
        // definitions in <code>setupInstantiationWithoutRetry</code> should
        // give cost infinity to those incomplete rule applications that will
        // never be instantiated (so that these applications can be removed from
        // the queue and do not have to be considered again).
        setupInstantiationWithoutRetry(d);

        // chrisg: The following rule, if active, must be applied delta rules.
        if (autoInductionEnabled()) {
            bindRuleSet(d, "auto_induction", -6500); // chrisg
        } else {
            bindRuleSet(d, "auto_induction", inftyConst()); // chrisg
        }

        // chrisg: The following rule is a beta rule that, if active, must have
        // a higher priority than other beta rules.
        if (autoInductionLemmaEnabled()) {
            bindRuleSet(d, "auto_induction_lemma", -300);
        } else {
            bindRuleSet(d, "auto_induction_lemma", inftyConst());
        }

        bindRuleSet(d, "information_flow_contract_appl", longConst(1000000));

        if (strategyProperties.contains(StrategyProperties.AUTO_INDUCTION_ON)
                || strategyProperties.contains(StrategyProperties.AUTO_INDUCTION_LEMMA_ON)) {
            bindRuleSet(d, "induction_var", 0);
        } else if (!autoInductionEnabled() && !autoInductionLemmaEnabled()) {
            bindRuleSet(d, "induction_var", inftyConst());
        } else {
            bindRuleSet(d, "induction_var", ifZero(
                applyTF(instOf("uSub"), IsInductionVariable.INSTANCE), longConst(0), inftyConst()));
        }

        return d;
    }

    private void setupSelectSimplification(final RuleSetDispatchFeature d) {
        bindRuleSet(d, "pull_out_select",
            // pull out select only if it can be simplified
            // (the heap term may not be the base heap or an anon heap
            // function symbol)
            add(applyTF("h",
                not(or(PrimitiveHeapTermFeature.create(heapLDT), AnonHeapTermFeature.INSTANCE))),
                ifZero(applyTF(FocusFormulaProjection.INSTANCE, ff.update), longConst(-4200),
                    longConst(-1900)),
                NonDuplicateAppModPositionFeature.INSTANCE));
        bindRuleSet(d, "apply_select_eq",
            // replace non-simplified select by the skolem constant
            // of the corresponding pull out; at least one select
            // needs to be not simplified yet; additional restrictions
            // in isApproved()
            ifZero(applyTF("s", not(rec(any(), SimplifiedSelectTermFeature.create(heapLDT)))),
                // together with the costs of apply_equations the
                // resulting costs are about -5700
                longConst(-1700)));
        bindRuleSet(d, "simplify_select",
            // simplify_select term in pulled out equation (right hand
            // side has to be a skolem constant which has been
            // introduced by a select pull out; left hand side needs
            // to be a select term on a non-base- and
            // non-anon-heap)
            add(applyTF("sk", IsSelectSkolemConstantTermFeature.INSTANCE),
                applyTF(sub(FocusProjection.INSTANCE, 0),
                    not(SimplifiedSelectTermFeature.create(heapLDT))),
                longConst(-5600)));
        bindRuleSet(d, "apply_auxiliary_eq",
            // replace skolem constant by it's computed value
            add(applyTF("t1", IsSelectSkolemConstantTermFeature.INSTANCE), longConst(-5500)));
        bindRuleSet(d, "hide_auxiliary_eq",
            // hide auxiliary equation after the skolem constants have
            // been replaced by it's computed value
            add(applyTF("auxiliarySK", IsSelectSkolemConstantTermFeature.INSTANCE),
                applyTF("result",
                    rec(any(),
                        add(SimplifiedSelectTermFeature.create(heapLDT), not(ff.ifThenElse)))),
                not(ContainsTermFeature.create(instOf("result"), instOf("auxiliarySK"))),
                longConst(-5400)));
        bindRuleSet(d, "hide_auxiliary_eq_const",
            // hide auxiliary equation after the skolem constatns have
            // been replaced by it's computed value
            add(applyTF("auxiliarySK", IsSelectSkolemConstantTermFeature.INSTANCE),
                longConst(-500)));
    }

    private void setUpStringNormalisation(RuleSetDispatchFeature d) {

        // translates an integer into its string representation
        bindRuleSet(d, "integerToString", -10000);

        // do not convert char to int when inside a string function
        // feature used to recognize if one is inside a string literal
        final SeqLDT seqLDT = getServices().getTypeConverter().getSeqLDT();
        final CharListLDT charListLDT = getServices().getTypeConverter().getCharListLDT();
        final BooleanLDT booleanLDT = getServices().getTypeConverter().getBooleanLDT();


        final TermFeature keepChar =
            or(op(seqLDT.getSeqSingleton()), or(op(charListLDT.getClIndexOfChar()),
                or(op(charListLDT.getClReplace()), op(charListLDT.getClLastIndexOfChar()))));

        bindRuleSet(d, "charLiteral_to_intLiteral",
            ifZero(isBelow(keepChar), inftyConst(), longConst(-100)));

        // establish normalform

        // tf below only for test
        final TermFeature anyLiteral = or(tf.charLiteral,
            or(tf.literal, op(booleanLDT.getFalseConst()), op(booleanLDT.getTrueConst())));

        final TermFeature seqLiteral = rec(anyLiteral, or(op(seqLDT.getSeqConcat()),
            or(op(seqLDT.getSeqSingleton()), or(anyLiteral, inftyTermConst()))));

        Feature belowModOpPenality = ifZero(isBelow(ff.modalOperator), longConst(500));

        bindRuleSet(d, "defOpsSeqEquality",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(add(applyTF("left", seqLiteral), applyTF("right", seqLiteral)),
                    longConst(1000), inftyConst()),
                belowModOpPenality));

        bindRuleSet(d, "defOpsConcat",
            add(NonDuplicateAppModPositionFeature.INSTANCE,
                ifZero(
                    or(applyTF("leftStr", not(seqLiteral)), applyTF("rightStr", not(seqLiteral))),
                    longConst(1000)
                // concat is often introduced for construction purposes,
                // we do not want to use its definition right at the
                // beginning
                ), belowModOpPenality));

        bindRuleSet(d, "stringsSimplify", longConst(-5000));

        final TermFeature charOrIntLiteral = or(tf.charLiteral, tf.literal,
            or(add(OperatorClassTF.create(SortDependingFunction.class), // XXX:
                // was CastFunctionSymbol.class
                sub(tf.literal)), inftyTermConst()));

        bindRuleSet(d, "defOpsReplaceInline",
            ifZero(add(applyTF("str", seqLiteral), applyTF("searchChar", charOrIntLiteral),
                applyTF("replChar", charOrIntLiteral)), longConst(-2500), inftyConst()));

        bindRuleSet(d, "defOpsReplace", add(NonDuplicateAppModPositionFeature.INSTANCE,
            ifZero(or(applyTF("str", not(seqLiteral)), applyTF("searchChar", not(charOrIntLiteral)),
                applyTF("replChar", not(charOrIntLiteral))), longConst(500), inftyConst()),
            belowModOpPenality));

        bindRuleSet(d, "stringsReduceSubstring",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(100)));

        bindRuleSet(d, "defOpsStartsEndsWith", longConst(250));

        bindRuleSet(d, "stringsConcatNotBothLiterals", ifZero(MatchedIfFeature.INSTANCE, ifZero(
            add(applyTF(instOf("leftStr"), seqLiteral), applyTF(instOf("rightStr"), seqLiteral)),
            inftyConst()), inftyConst()));

        bindRuleSet(d, "stringsReduceConcat", longConst(100));

        bindRuleSet(d, "stringsReduceOrMoveOutsideConcat",
            ifZero(NonDuplicateAppModPositionFeature.INSTANCE, longConst(800), inftyConst()));

        bindRuleSet(d, "stringsMoveReplaceInside",
            ifZero(NonDuplicateAppModPositionFeature.INSTANCE, longConst(400), inftyConst()));


        bindRuleSet(d, "stringsExpandDefNormalOp", longConst(500));

        bindRuleSet(d, "stringsContainsDefInline", SumFeature
                .createSum(EqNonDuplicateAppFeature.INSTANCE, longConst(1000)));
    }

    private void setupReplaceKnown(RuleSetDispatchFeature d) {
        final Feature commonF =
            add(ifZero(MatchedIfFeature.INSTANCE, DiffFindAndIfFeature.INSTANCE), longConst(-5000),
                add(DiffFindAndReplacewithFeature.INSTANCE,
                    ScaleFeature.createScaled(CountMaxDPathFeature.INSTANCE, 10.0)));

        bindRuleSet(d, "replace_known_left", commonF);
        bindRuleSet(d, "replace_known_right",
            add(commonF, ifZero(DirectlyBelowSymbolFeature.create(Junctor.IMP, 1), longConst(100),
                ifZero(DirectlyBelowSymbolFeature.create(Equality.EQV), longConst(100)))));
    }

    private void setupUserTaclets(RuleSetDispatchFeature d) {
        for (int i = 1; i <= StrategyProperties.USER_TACLETS_NUM; ++i) {
            final String userTacletsProbs =
                strategyProperties.getProperty(StrategyProperties.userTacletsOptionsKey(i));
            if (StrategyProperties.USER_TACLETS_LOW.equals(userTacletsProbs)) {
                bindRuleSet(d, "userTaclets" + i, 10000);
            } else if (StrategyProperties.USER_TACLETS_HIGH.equals(userTacletsProbs)) {
                bindRuleSet(d, "userTaclets" + i, -50);
            } else {
                bindRuleSet(d, "userTaclets" + i, inftyConst());
            }
        }
    }

    private void setupSystemInvariantSimp(RuleSetDispatchFeature d) {
        bindRuleSet(d, "system_invariant",
            ifZero(MatchedIfFeature.INSTANCE, add(applyTF("negLit", tf.negLiteral),
                applyTFNonStrict("nonNegLit", tf.nonNegLiteral))));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Queries for the active taclet options
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private boolean arithNonLinInferences() {
        return StrategyProperties.NON_LIN_ARITH_COMPLETION.equals(
            strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY));
    }

    protected boolean arithDefOps() {
        return StrategyProperties.NON_LIN_ARITH_DEF_OPS.equals(
            strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY))
                || StrategyProperties.NON_LIN_ARITH_COMPLETION.equals(
                    strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY));
    }

    private boolean instQuantifiersWithQueries() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    private boolean quantifiersMightSplit() {
        return StrategyProperties.QUANTIFIERS_INSTANTIATE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))
                || StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS.equals(
                    strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    private Feature allowQuantifierSplitting() {
        if (StrategyProperties.QUANTIFIERS_INSTANTIATE.equals(
            strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            return longConst(0);
        }
        if (StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS.equals(
            strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            return sequentContainsNoPrograms();
        }
        return inftyConst();
    }

    private boolean quantifierInstantiatedEnabled() {
        return !StrategyProperties.QUANTIFIERS_NONE
                .equals(strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY));
    }

    private boolean classAxiomDelayedApplication() {
        String classAxiomSetting =
            strategyProperties.getProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY);
        return StrategyProperties.CLASS_AXIOM_DELAYED.equals(classAxiomSetting);
    }

    private boolean classAxiomApplicationEnabled() {
        String classAxiomSetting =
            strategyProperties.getProperty(StrategyProperties.CLASS_AXIOM_OPTIONS_KEY);
        return !StrategyProperties.CLASS_AXIOM_OFF.equals(classAxiomSetting);
    }

    private boolean autoInductionEnabled() { // chrisg
        // Negated!
        return !StrategyProperties.AUTO_INDUCTION_OFF.equals(
            strategyProperties.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY));
    }

    private boolean autoInductionLemmaEnabled() { // chrisg
        final String prop =
            strategyProperties.getProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY);
        return prop.equals(StrategyProperties.AUTO_INDUCTION_LEMMA_ON)
                || prop.equals(StrategyProperties.AUTO_INDUCTION_RESTRICTED);
        /*
         * return StrategyProperties.AUTO_INDUCTION_LEMMA_ON.equals ( strategyProperties.getProperty
         * ( StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY ) );
         */
    }

    private Feature allowSplitting(ProjectionToTerm focus) {
        if (normalSplitting()) {
            return longConst(0);
        }
        if (StrategyProperties.SPLITTING_DELAYED
                .equals(strategyProperties.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY))) {
            return or(applyTF(focus, ContainsExecutableCodeTermFeature.PROGRAMS),
                sequentContainsNoPrograms());
        }
        // else: SPLITTING_OFF
        return applyTF(focus, ContainsExecutableCodeTermFeature.PROGRAMS);
    }

    private boolean normalSplitting() {
        return StrategyProperties.SPLITTING_NORMAL
                .equals(strategyProperties.getProperty(StrategyProperties.SPLITTING_OPTIONS_KEY));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Application of beta- and cut-rules to handle disjunctions
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private void setupSplitting(RuleSetDispatchFeature d) {
        final TermBuffer subFor = new TermBuffer();
        final Feature noCutsAllowed =
            sum(subFor, AllowedCutPositionsGenerator.INSTANCE, not(applyTF(subFor, ff.cutAllowed)));
        bindRuleSet(d, "beta",
            SumFeature.createSum(noCutsAllowed,
                ifZero(PurePosDPathFeature.INSTANCE, longConst(-200)),
                ScaleFeature.createScaled(CountPosDPathFeature.INSTANCE, -3.0),
                ScaleFeature.createScaled(CountMaxDPathFeature.INSTANCE, 10.0), longConst(20)));
        TermBuffer superF = new TermBuffer();
        final ProjectionToTerm splitCondition = sub(FocusProjection.INSTANCE, 0);
        bindRuleSet(d, "split_cond", add(// do not split over formulas containing auxiliary
                                         // variables
            applyTF(FocusProjection.INSTANCE,
                rec(any(), not(IsSelectSkolemConstantTermFeature.INSTANCE))),
            // prefer splits when condition has quantifiers (less
            // likely to be simplified away)
            applyTF(splitCondition,
                rec(ff.quantifiedFor, ifZero(ff.quantifiedFor, longTermConst(-10)))),
            FindDepthFeature.INSTANCE, // prefer top level splits
            ScaleFeature.createAffine(countOccurrences(splitCondition), -10, 10),
            sum(superF, SuperTermGenerator.upwards(any(), getServices()),
                applyTF(superF, not(ff.elemUpdate))),
            ifZero(applyTF(FocusProjection.INSTANCE, ContainsExecutableCodeTermFeature.PROGRAMS),
                longConst(-100), longConst(25))));
        ProjectionToTerm cutFormula = instOf("cutFormula");
        Feature countOccurrencesInSeq =
            ScaleFeature.createAffine(countOccurrences(cutFormula), -10, 10);
        bindRuleSet(d, "cut_direct",
            SumFeature
                    .createSum(
                        not(TopLevelFindFeature.ANTEC_OR_SUCC_WITH_UPDATE),
                        AllowedCutPositionFeature.INSTANCE,
                        ifZero(
                            NotBelowQuantifierFeature.INSTANCE, add(
                                applyTF(cutFormula, add(ff.cutAllowed,
                                    // do not cut over formulas containing
                                    // auxiliary variables
                                    rec(any(),
                                        not(IsSelectSkolemConstantTermFeature.INSTANCE)))),
                                // prefer cuts over "something = null"
                                ifZero(
                                    applyTF(FocusProjection.INSTANCE,
                                        opSub(tf.eq, any(), vf.nullTerm)),
                                    longConst(-5), longConst(0)),
                                // punish cuts over formulas containing anon heap functions
                                ifZero(
                                    applyTF(cutFormula,
                                        rec(any(), not(AnonHeapTermFeature.INSTANCE))),
                                    longConst(0), longConst(1000)),
                                countOccurrencesInSeq, // standard costs
                                longConst(100)),
                            SumFeature // check for cuts below quantifiers
                                    .createSum(applyTF(cutFormula, ff.cutAllowedBelowQuantifier),
                                        applyTF(FocusFormulaProjection.INSTANCE,
                                            ff.quantifiedClauseSet),
                                        ifZero(allowQuantifierSplitting(), longConst(0),
                                            longConst(100))))));
    }

    private void setupSplittingApproval(RuleSetDispatchFeature d) {
        bindRuleSet(d, "beta", allowSplitting(FocusFormulaProjection.INSTANCE));

        bindRuleSet(d, "split_cond", allowSplitting(FocusProjection.INSTANCE));

        final TermBuffer subFor = new TermBuffer();
        final Feature compareCutAllowed = ifZero(applyTF(subFor, ff.cutAllowed),
            leq(applyTF("cutFormula", ff.cutPriority), applyTF(subFor, ff.cutPriority)));

        final Feature noBetterCut =
            sum(subFor, AllowedCutPositionsGenerator.INSTANCE, compareCutAllowed);

        bindRuleSet(d, "cut_direct", add(allowSplitting(FocusFormulaProjection.INSTANCE),
            ifZero(NotBelowQuantifierFeature.INSTANCE, noBetterCut)));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Application of equations
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private void setupApplyEq(RuleSetDispatchFeature d, IntegerLDT numbers) {
        final TermBuffer equation = new TermBuffer();
        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();

        // applying equations less deep/less leftish in terms/formulas is
        // preferred
        // this is important for reducing polynomials (start with the biggest
        // summands)
        bindRuleSet(d, "apply_equations",
            SumFeature.createSum(ifZero(applyTF(FocusProjection.create(0), tf.intF),
                add(applyTF(FocusProjection.create(0), tf.monomial),
                    ScaleFeature.createScaled(FindRightishFeature.create(numbers), 5.0))),
                ifZero(MatchedIfFeature.INSTANCE,
                    add(CheckApplyEqFeature.INSTANCE, let(equation, AssumptionProjection.create(0),
                        add(not(applyTF(equation, ff.update)),
                            // there might be updates in
                            // front of the assumption
                            // formula; in this case we wait
                            // until the updates have
                            // been applied
                            let(left, sub(equation, 0),
                                let(right, sub(equation, 1), ifZero(applyTF(left, tf.intF),
                                    add(applyTF(left, tf.nonNegOrNonCoeffMonomial),
                                        applyTF(right, tf.polynomial),
                                        MonomialsSmallerThanFeature.create(right, left, numbers)),
                                    TermSmallerThanFeature.create(right, left)))))))),
                longConst(-4000)));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Normalisation of formulas; this is mostly a pre-processing step for
    // handling quantified formulas
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private void setupFormulaNormalisation(RuleSetDispatchFeature d, IntegerLDT numbers,
            LocSetLDT locSetLDT) {

        bindRuleSet(d, "negationNormalForm", add(not(NotBelowBinderFeature.INSTANCE),
            longConst(-500), ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 10.0)));

        bindRuleSet(d, "moveQuantToLeft",
            add(quantifiersMightSplit() ? longConst(0)
                    : applyTF(FocusFormulaProjection.INSTANCE, ff.quantifiedPureLitConjDisj),
                longConst(-550)));

        bindRuleSet(d, "conjNormalForm",
            ifZero(
                add(or(FocusInAntecFeature.INSTANCE, NotBelowQuantifierFeature.INSTANCE),
                    NotInScopeOfModalityFeature.INSTANCE),
                add(longConst(-150), ScaleFeature.createScaled(FindDepthFeature.INSTANCE, 20)),
                inftyConst()));

        bindRuleSet(d, "setEqualityBlastingRight", longConst(-100));

        bindRuleSet(d, "cnf_setComm",
            add(SetsSmallerThanFeature.create(instOf("commRight"), instOf("commLeft"), locSetLDT),
                NotInScopeOfModalityFeature.INSTANCE, longConst(-800)));

        bindRuleSet(d, "elimQuantifier", -1000);
        bindRuleSet(d, "elimQuantifierWithCast", 50);

        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();
        bindRuleSet(d, "apply_equations_andOr",
            add(let(left, instOf("applyEqLeft"),
                let(right, instOf("applyEqRight"), ifZero(applyTF(left, tf.intF),
                    add(applyTF(left, tf.nonNegOrNonCoeffMonomial), applyTF(right, tf.polynomial),
                        MonomialsSmallerThanFeature.create(right, left, numbers)),
                    TermSmallerThanFeature.create(right, left)))),
                longConst(-150)));

        bindRuleSet(d, "distrQuantifier",
            add(or(
                applyTF(FocusProjection.create(0),
                    add(ff.quantifiedClauseSet, not(opSub(Quantifier.ALL, ff.orF)),
                        EliminableQuantifierTF.INSTANCE)),
                SumFeature.createSum(OnlyInScopeOfQuantifiersFeature.INSTANCE,
                    SplittableQuantifiedFormulaFeature.INSTANCE,
                    ifZero(FocusInAntecFeature.INSTANCE,
                        applyTF(FocusProjection.create(0), sub(ff.andF)),
                        applyTF(FocusProjection.create(0), sub(ff.orF))))),
                longConst(-300)));

        bindRuleSet(d, "swapQuantifiers",
            add(applyTF(FocusProjection.create(0), add(ff.quantifiedClauseSet,
                EliminableQuantifierTF.INSTANCE, sub(not(EliminableQuantifierTF.INSTANCE)))),
                longConst(-300)));

        // category "conjunctive normal form"

        bindRuleSet(d, "cnf_orComm",
            SumFeature.createSum(applyTF("commRight", ff.clause),
                applyTFNonStrict("commResidue", ff.clauseSet),
                or(applyTF("commLeft", ff.andF),
                    add(applyTF("commLeft", ff.literal),
                        literalsSmallerThan("commRight", "commLeft", numbers))),
                longConst(-100)));

        bindRuleSet(d, "cnf_orAssoc",
            SumFeature.createSum(applyTF("assoc0", ff.clause),
                applyTF("assoc1", ff.clause), applyTF("assoc2", ff.literal), longConst(-80)));

        bindRuleSet(d, "cnf_andComm",
            SumFeature.createSum(applyTF("commLeft", ff.clause),
                applyTF("commRight", ff.clauseSet), applyTFNonStrict("commResidue", ff.clauseSet),
                // at least one of the subformulas has to be a literal;
                // otherwise,
                // sorting is not likely to have any big effect
                ifZero(
                    add(applyTF("commLeft", not(ff.literal)),
                        applyTF("commRight", rec(ff.andF, not(ff.literal)))),
                    longConst(100), longConst(-60)),
                clausesSmallerThan("commRight", "commLeft", numbers)));

        bindRuleSet(d, "cnf_andAssoc",
            SumFeature.createSum(applyTF("assoc0", ff.clauseSet),
                applyTF("assoc1", ff.clauseSet), applyTF("assoc2", ff.clause), longConst(-10)));

        bindRuleSet(d, "cnf_dist",
            SumFeature.createSum(applyTF("distRight0", ff.clauseSet),
                applyTF("distRight1", ff.clauseSet), ifZero(applyTF("distLeft", ff.clause),
                    longConst(-15), applyTF("distLeft", ff.clauseSet)),
                longConst(-35)));

        final TermBuffer superFor = new TermBuffer();
        final Feature onlyBelowQuanAndOr =
            sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                applyTF(superFor, or(ff.quantifiedFor, ff.andF, ff.orF)));

        final Feature belowUnskolemisableQuantifier = ifZero(FocusInAntecFeature.INSTANCE,
            not(sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                not(applyTF(superFor, op(Quantifier.ALL))))),
            not(sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                not(applyTF(superFor, op(Quantifier.EX))))));

        bindRuleSet(d, "cnf_expandIfThenElse", add(not(NotBelowQuantifierFeature.INSTANCE),
            onlyBelowQuanAndOr, belowUnskolemisableQuantifier));

        final Feature pullOutQuantifierAllowed =
            add(not(NotBelowQuantifierFeature.INSTANCE), onlyBelowQuanAndOr, applyTF(
                FocusProjection.create(0), sub(ff.quantifiedClauseSet, ff.quantifiedClauseSet)));

        bindRuleSet(d, "pullOutQuantifierUnifying", -20);

        bindRuleSet(d, "pullOutQuantifierAll", add(pullOutQuantifierAllowed,
            ifZero(FocusInAntecFeature.INSTANCE, longConst(-20), longConst(-40))));

        bindRuleSet(d, "pullOutQuantifierEx", add(pullOutQuantifierAllowed,
            ifZero(FocusInAntecFeature.INSTANCE, longConst(-40), longConst(-20))));
    }

    private Feature clausesSmallerThan(String smaller, String bigger, IntegerLDT numbers) {
        return ClausesSmallerThanFeature.create(instOf(smaller), instOf(bigger), numbers);
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Heuristic instantiation of quantified formulas
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private void setupQuantifierInstantiation(RuleSetDispatchFeature d) {
        if (quantifierInstantiatedEnabled()) {
            final TermBuffer varInst = new TermBuffer();
            final Feature branchPrediction = InstantiationCostScalerFeature
                    .create(InstantiationCost.create(varInst), allowQuantifierSplitting());

            bindRuleSet(d, "gamma",
                SumFeature.createSum(FocusInAntecFeature.INSTANCE,
                    applyTF(FocusProjection.create(0),
                        add(ff.quantifiedClauseSet,
                            instQuantifiersWithQueries() ? longTermConst(0)
                                    : ff.notContainsExecutable)),
                    forEach(varInst, HeuristicInstantiation.INSTANCE,
                        add(instantiate("t", varInst), branchPrediction, longConst(10)))));
            final TermBuffer splitInst = new TermBuffer();

            bindRuleSet(d, "triggered",
                SumFeature.createSum(forEach(splitInst, TriggeredInstantiations.create(true),
                    add(instantiateTriggeredVariable(splitInst), longConst(500))),
                    longConst(1500)));

        } else {
            bindRuleSet(d, "gamma", inftyConst());
            bindRuleSet(d, "triggered", inftyConst());
        }
    }

    private void setupQuantifierInstantiationApproval(RuleSetDispatchFeature d) {
        if (quantifierInstantiatedEnabled()) {
            final TermBuffer varInst = new TermBuffer();

            bindRuleSet(d, "gamma", add(isInstantiated("t"),
                not(sum(varInst, HeuristicInstantiation.INSTANCE, not(eq(instOf("t"), varInst)))),
                InstantiationCostScalerFeature.create(InstantiationCost.create(instOf("t")),
                    longConst(0))));

            final TermBuffer splitInst = new TermBuffer();
            bindRuleSet(d, "triggered",
                add(isTriggerVariableInstantiated(),
                    not(sum(splitInst, TriggeredInstantiations.create(false),
                        not(eq(instOfTriggerVariable(), splitInst))))));
        } else {
            bindRuleSet(d, "gamma", inftyConst());
            bindRuleSet(d, "triggered", inftyConst());
        }
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Handling of arithmetic
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private void setupArithPrimaryCategories(RuleSetDispatchFeature d) {
        // Gaussian elimination + Euclidian algorithm for linear equations;
        // Buchberger's algorithmus for handling polynomial equations over
        // the integers

        bindRuleSet(d, "polySimp_expand", -4500);
        bindRuleSet(d, "polySimp_directEquations", -3000);
        bindRuleSet(d, "polySimp_pullOutGcd", -2250);
        bindRuleSet(d, "polySimp_leftNonUnit", -2000);
        bindRuleSet(d, "polySimp_saturate", 0);

        // Omega test for handling linear arithmetic and inequalities over the
        // integers; cross-multiplication + case distinctions for nonlinear
        // inequalities

        bindRuleSet(d, "inEqSimp_expand", -4400);
        bindRuleSet(d, "inEqSimp_directInEquations", -2900);
        bindRuleSet(d, "inEqSimp_propagation", -2400);
        bindRuleSet(d, "inEqSimp_pullOutGcd", -2150);
        bindRuleSet(d, "inEqSimp_saturate", -1900);
        bindRuleSet(d, "inEqSimp_forNormalisation", -1100);
        bindRuleSet(d, "inEqSimp_special_nonLin", -1400);

        if (arithNonLinInferences()) {
            bindRuleSet(d, "inEqSimp_nonLin", IN_EQ_SIMP_NON_LIN_COST);
        } else {
            bindRuleSet(d, "inEqSimp_nonLin", inftyConst());
        }
        // polynomial division, simplification of fractions and mods
        bindRuleSet(d, "polyDivision", POLY_DIVISION_COST);

    }

    private void setupPolySimp(RuleSetDispatchFeature d, IntegerLDT numbers) {

        // category "expansion" (normalising polynomial terms)

        bindRuleSet(d, "polySimp_elimSubNeg", longConst(-120));

        bindRuleSet(d, "polySimp_homo",
            add(applyTF("homoRight", add(not(tf.zeroLiteral), tf.polynomial)),
                or(applyTF("homoLeft", or(tf.addF, tf.negMonomial)),
                    not(monSmallerThan("homoRight", "homoLeft", numbers))),
                longConst(-120)));

        bindRuleSet(d, "polySimp_pullOutFactor", add(applyTFNonStrict("pullOutLeft", tf.literal),
            applyTFNonStrict("pullOutRight", tf.literal), longConst(-120)));

        bindRuleSet(d, "polySimp_elimOneLeft", -120);

        bindRuleSet(d, "polySimp_elimOneRight", -120);

        bindRuleSet(d, "polySimp_mulOrder", add(applyTF("commRight", tf.monomial), or(
            applyTF("commLeft", tf.addF),
            add(applyTF("commLeft", tf.atom), atomSmallerThan("commLeft", "commRight", numbers))),
            longConst(-100)));

        bindRuleSet(d, "polySimp_mulAssoc",
            SumFeature.createSum(applyTF("mulAssocMono0", tf.monomial),
                applyTF("mulAssocMono1", tf.monomial), applyTF("mulAssocAtom", tf.atom),
                longConst(-80)));

        bindRuleSet(d, "polySimp_addOrder",
            SumFeature.createSum(applyTF("commLeft", tf.monomial),
                applyTF("commRight", tf.polynomial),
                monSmallerThan("commRight", "commLeft", numbers), longConst(-60)));

        bindRuleSet(d, "polySimp_addAssoc",
            SumFeature.createSum(applyTF("addAssocPoly0", tf.polynomial),
                applyTF("addAssocPoly1", tf.polynomial), applyTF("addAssocMono", tf.monomial),
                longConst(-10)));

        bindRuleSet(d, "polySimp_dist",
            SumFeature.createSum(applyTF("distSummand0", tf.polynomial),
                applyTF("distSummand1", tf.polynomial),
                ifZero(applyTF("distCoeff", tf.monomial), longConst(-15),
                    applyTF("distCoeff", tf.polynomial)),
                applyTF("distSummand0", tf.polynomial),

                applyTF("distSummand1", tf.polynomial), longConst(-35)));

        // category "direct equations"

        bindRuleSet(d, "polySimp_balance",
            SumFeature
                    .createSum(applyTF("sepResidue", tf.polynomial),
                        ifZero(isInstantiated("sepPosMono"),
                            add(applyTF("sepPosMono", tf.nonNegMonomial),
                                monSmallerThan("sepResidue", "sepPosMono", numbers))),
                        ifZero(isInstantiated("sepNegMono"),
                            add(applyTF("sepNegMono", tf.negMonomial),
                                monSmallerThan("sepResidue", "sepNegMono", numbers))),
                        longConst(-30)));

        bindRuleSet(d, "polySimp_normalise", add(applyTF("invertRight", tf.zeroLiteral),
            applyTF("invertLeft", tf.negMonomial), longConst(-30)));

        // application of equations: some specialised rules that handle
        // monomials and their coefficients properly

        final TermBuffer eqLeft = new TermBuffer();
        final TermBuffer focus = new TermBuffer();

        final TermFeature atLeastTwoLCEquation =
            opSub(Equality.EQUALS, opSub(tf.mul, tf.atom, tf.atLeastTwoLiteral), tf.intF);

        final Feature validEqApplication = add(not(eq(eqLeft, focus)),
            // otherwise, the normal equation rules can and should
            // be used
            ifZero(applyTF(AssumptionProjection.create(0), atLeastTwoLCEquation),
                add(FocusInAntecFeature.INSTANCE,
                    applyTF(FocusFormulaProjection.INSTANCE, atLeastTwoLCEquation))),
            ReducibleMonomialsFeature.createReducible(focus, eqLeft));

        final Feature eqMonomialFeature = add(not(DirectlyBelowSymbolFeature.create(tf.mul)),
            ifZero(MatchedIfFeature.INSTANCE, let(focus, FocusProjection.create(0),
                let(eqLeft, sub(AssumptionProjection.create(0), 0), validEqApplication))));

        bindRuleSet(d, "polySimp_applyEq", add(eqMonomialFeature, longConst(1)));

        bindRuleSet(d, "polySimp_applyEqRigid", add(eqMonomialFeature, longConst(2)));

        //
        bindRuleSet(d, "defOps_expandModulo",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-600)));

        // category "saturate"

        bindRuleSet(d, "polySimp_critPair",
            ifZero(MatchedIfFeature.INSTANCE, add(monSmallerThan("cpLeft1", "cpLeft2", numbers),
                not(TrivialMonomialLCRFeature.create(instOf("cpLeft1"), instOf("cpLeft2"))))));
    }

    // For taclets that need instantiation, but where the instantiation is
    // deterministic and does not have to be repeated at a later point, we
    // setup the same feature terms as in the instantiation method. The
    // definitions in <code>setupInstantiationWithoutRetry</code> should
    // give cost infinity to those incomplete rule applications that will
    // never be instantiated (so that these applications can be removed from
    // the queue and do not have to be considered again).
    private void setupPolySimpInstantiationWithoutRetry(RuleSetDispatchFeature d) {
        final IntegerLDT numbers = getServices().getTypeConverter().getIntegerLDT();

        // category "direct equations"

        setupPullOutGcd(d, "polySimp_pullOutGcd", false);

        // category "polynomial division"

        setupDivModDivision(d);

        // category "handling of equations with non-unit-coefficients on
        // left-hand side"

        bindRuleSet(d, "polySimp_newSym",
            ifZero(not(isInstantiated("newSymDef")), SumFeature.createSum(
                applyTF("newSymLeft", tf.atom), applyTF("newSymLeftCoeff", tf.atLeastTwoLiteral),
                applyTF("newSymRight", tf.polynomial), instantiate("newSymDef",
                    MonomialColumnOp.create(instOf("newSymLeftCoeff"), instOf("newSymRight"))))));

        final TermBuffer divisor = new TermBuffer();
        final TermBuffer dividend = new TermBuffer();

        bindRuleSet(d, "polySimp_applyEqPseudo",
            add(applyTF("aePseudoTargetLeft", tf.monomial),
                applyTF("aePseudoTargetRight", tf.polynomial),
                ifZero(MatchedIfFeature.INSTANCE,
                    SumFeature.createSum(DiffFindAndIfFeature.INSTANCE,
                        applyTF("aePseudoLeft", add(tf.nonCoeffMonomial, not(tf.atom))),
                        applyTF("aePseudoLeftCoeff", tf.atLeastTwoLiteral),
                        applyTF("aePseudoRight", tf.polynomial),
                        MonomialsSmallerThanFeature.create(instOf("aePseudoRight"),
                            instOf("aePseudoLeft"), numbers),
                        let(divisor, instOf("aePseudoLeft"),
                            let(dividend, instOf("aePseudoTargetLeft"),
                                add(ReducibleMonomialsFeature.createReducible(dividend, divisor),
                                    instantiate("aePseudoTargetFactor",
                                        ReduceMonomialsProjection.create(dividend, divisor)))))))));
    }

    private void setupNewSymApproval(RuleSetDispatchFeature d, IntegerLDT numbers) {
        final TermBuffer antecFor = new TermBuffer();
        final Feature columnOpEq = applyTF(antecFor,
            opSub(tf.eq, opSub(tf.mul, tf.atom, tf.atLeastTwoLiteral), tf.polynomial));
        final Feature biggerLeftSide = MonomialsSmallerThanFeature.create(instOf("newSymLeft"),
            subAt(antecFor, PosInTerm.getTopLevel().down(0).down(0)), numbers);
        bindRuleSet(d, "polySimp_newSym", add(isInstantiated("newSymDef"), sum(antecFor,
            SequentFormulasGenerator.antecedent(), not(add(columnOpEq, biggerLeftSide)))));
    }

    private void setupPullOutGcd(RuleSetDispatchFeature d, String ruleSet, boolean roundingUp) {
        final TermBuffer gcd = new TermBuffer();

        final Feature instantiateDivs;
        if (roundingUp) {
            instantiateDivs = add(
                instantiate("elimGcdLeftDiv",
                    DividePolynomialsProjection.createRoundingUp(gcd, instOf("elimGcdLeft"))),
                instantiate("elimGcdRightDiv",
                    DividePolynomialsProjection.createRoundingUp(gcd, instOf("elimGcdRight"))));
        } else {
            instantiateDivs = add(
                instantiate("elimGcdLeftDiv",
                    DividePolynomialsProjection.createRoundingDown(gcd, instOf("elimGcdLeft"))),
                instantiate("elimGcdRightDiv",
                    DividePolynomialsProjection.createRoundingDown(gcd, instOf("elimGcdRight"))));
        }
        bindRuleSet(d, ruleSet,
            add(applyTF("elimGcdLeft", tf.nonNegMonomial), applyTF("elimGcdRight", tf.polynomial),
                let(gcd, CoeffGcdProjection.create(instOf("elimGcdLeft"), instOf("elimGcdRight")),
                    add(applyTF(gcd, tf.atLeastTwoLiteral), instantiate("elimGcd", gcd),
                        instantiateDivs))));
    }

    private void setupInEqSimp(RuleSetDispatchFeature d, IntegerLDT numbers) {

        // category "expansion" (normalising inequations)

        bindRuleSet(d, "inEqSimp_moveLeft", -90);

        bindRuleSet(d, "inEqSimp_makeNonStrict", -80);

        bindRuleSet(d, "inEqSimp_commute",
            SumFeature.createSum(applyTF("commRight", tf.monomial),
                applyTF("commLeft", tf.polynomial),
                monSmallerThan("commLeft", "commRight", numbers), longConst(-40)));

        // this is copied from "polySimp_homo"
        bindRuleSet(d, "inEqSimp_homo",
            add(applyTF("homoRight", add(not(tf.zeroLiteral), tf.polynomial)),
                or(applyTF("homoLeft", or(tf.addF, tf.negMonomial)),
                    not(monSmallerThan("homoRight", "homoLeft", numbers)))));

        // category "direct inequations"

        // this is copied from "polySimp_balance"
        bindRuleSet(d, "inEqSimp_balance",
            add(applyTF("sepResidue", tf.polynomial),
                ifZero(isInstantiated("sepPosMono"),
                    add(applyTF("sepPosMono", tf.nonNegMonomial),
                        monSmallerThan("sepResidue", "sepPosMono", numbers))),
                ifZero(isInstantiated("sepNegMono"), add(applyTF("sepNegMono", tf.negMonomial),
                    monSmallerThan("sepResidue", "sepNegMono", numbers)))));

        // this is copied from "polySimp_normalise"
        bindRuleSet(d, "inEqSimp_normalise",
            add(applyTF("invertRight", tf.zeroLiteral), applyTF("invertLeft", tf.negMonomial)));

        // category "saturate"

        bindRuleSet(d, "inEqSimp_antiSymm", longConst(-20));

        bindRuleSet(d, "inEqSimp_exactShadow",
            SumFeature.createSum(applyTF("esLeft", tf.nonCoeffMonomial),
                applyTFNonStrict("esCoeff2", tf.nonNegLiteral), applyTF("esRight2", tf.polynomial),
                ifZero(MatchedIfFeature.INSTANCE,
                    SumFeature.createSum(applyTFNonStrict("esCoeff1", tf.nonNegLiteral),
                        applyTF("esRight1", tf.polynomial),
                        not(PolynomialValuesCmpFeature.leq(instOf("esRight2"), instOf("esRight1"),
                            instOfNonStrict("esCoeff1"), instOfNonStrict("esCoeff2")))))));

        // category "propagation"

        bindRuleSet(d, "inEqSimp_contradInEqs",
            add(applyTF("contradLeft", tf.monomial),
                ifZero(MatchedIfFeature.INSTANCE,
                    SumFeature.createSum(DiffFindAndIfFeature.INSTANCE,
                        applyTF("contradRightSmaller", tf.polynomial),
                        applyTF("contradRightBigger", tf.polynomial),
                        applyTFNonStrict("contradCoeffSmaller", tf.posLiteral),
                        applyTFNonStrict("contradCoeffBigger", tf.posLiteral),
                        PolynomialValuesCmpFeature.lt(instOf("contradRightSmaller"),
                            instOf("contradRightBigger"), instOfNonStrict("contradCoeffBigger"),
                            instOfNonStrict("contradCoeffSmaller"))))));

        bindRuleSet(d, "inEqSimp_contradEqs",
            add(applyTF("contradLeft", tf.monomial),
                ifZero(MatchedIfFeature.INSTANCE,
                    SumFeature.createSum(applyTF("contradRightSmaller", tf.polynomial),
                        applyTF("contradRightBigger", tf.polynomial), PolynomialValuesCmpFeature
                                .lt(instOf("contradRightSmaller"), instOf("contradRightBigger")))),
                longConst(-60)));

        bindRuleSet(d, "inEqSimp_strengthen", longConst(-30));

        bindRuleSet(d, "inEqSimp_subsumption",
            add(applyTF("subsumLeft", tf.monomial),
                ifZero(MatchedIfFeature.INSTANCE,
                    SumFeature.createSum(DiffFindAndIfFeature.INSTANCE,
                        applyTF("subsumRightSmaller", tf.polynomial),
                        applyTF("subsumRightBigger", tf.polynomial),
                        applyTFNonStrict("subsumCoeffSmaller", tf.posLiteral),
                        applyTFNonStrict("subsumCoeffBigger", tf.posLiteral),
                        PolynomialValuesCmpFeature.leq(instOf("subsumRightSmaller"),
                            instOf("subsumRightBigger"), instOfNonStrict("subsumCoeffBigger"),
                            instOfNonStrict("subsumCoeffSmaller"))))));

        // category "handling of non-linear inequations"

        if (arithNonLinInferences()) {
            setupMultiplyInequations(d, longConst(100));

            bindRuleSet(d, "inEqSimp_split_eq", add(TopLevelFindFeature.SUCC, longConst(-100)));

            bindRuleSet(d, "inEqSimp_signCases", not(isInstantiated("signCasesLeft")));
        }

        // category "normalisation of formulas"
        // (e.g., quantified formulas, where the normal sequent calculus
        // does not do any normalisation)

        bindRuleSet(d, "inEqSimp_and_contradInEqs",
            SumFeature.createSum(applyTF("contradLeft", tf.monomial),
                applyTF("contradRightSmaller", tf.polynomial),
                applyTF("contradRightBigger", tf.polynomial), PolynomialValuesCmpFeature
                        .lt(instOf("contradRightSmaller"), instOf("contradRightBigger"))));

        bindRuleSet(d, "inEqSimp_andOr_subsumption",
            SumFeature.createSum(applyTF("subsumLeft", tf.monomial),
                applyTF("subsumRightSmaller", tf.polynomial),
                applyTF("subsumRightBigger", tf.polynomial), PolynomialValuesCmpFeature
                        .leq(instOf("subsumRightSmaller"), instOf("subsumRightBigger"))));

        bindRuleSet(d, "inEqSimp_and_subsumptionEq",
            SumFeature.createSum(applyTF("subsumLeft", tf.monomial),
                applyTF("subsumRightSmaller", tf.polynomial),
                applyTF("subsumRightBigger", tf.polynomial), PolynomialValuesCmpFeature
                        .lt(instOf("subsumRightSmaller"), instOf("subsumRightBigger"))));

        final TermBuffer one = new TermBuffer();
        one.setContent(getServices().getTermBuilder().zTerm("1"));
        final TermBuffer two = new TermBuffer();
        two.setContent(getServices().getTermBuilder().zTerm("2"));

        bindRuleSet(d, "inEqSimp_or_tautInEqs",
            SumFeature.createSum(applyTF("tautLeft", tf.monomial),
                applyTF("tautRightSmaller", tf.polynomial),
                applyTF("tautRightBigger", tf.polynomial),
                PolynomialValuesCmpFeature.leq(instOf("tautRightSmaller"),
                    opTerm(numbers.getAdd(), one, instOf("tautRightBigger")))));

        bindRuleSet(d, "inEqSimp_or_weaken",
            SumFeature.createSum(applyTF("weakenLeft", tf.monomial),
                applyTF("weakenRightSmaller", tf.polynomial),
                applyTF("weakenRightBigger", tf.polynomial),
                PolynomialValuesCmpFeature.eq(
                    opTerm(numbers.getAdd(), one, instOf("weakenRightSmaller")),
                    instOf("weakenRightBigger"))));

        bindRuleSet(d, "inEqSimp_or_antiSymm",
            SumFeature.createSum(applyTF("antiSymmLeft", tf.monomial),
                applyTF("antiSymmRightSmaller", tf.polynomial),
                applyTF("antiSymmRightBigger", tf.polynomial),
                PolynomialValuesCmpFeature.eq(
                    opTerm(numbers.getAdd(), two, instOf("antiSymmRightSmaller")),
                    instOf("antiSymmRightBigger"))));

    }

    private void setupMultiplyInequations(RuleSetDispatchFeature d, Feature notAllowedF) {
        final TermBuffer intRel = new TermBuffer();

        /*
         * final Feature partiallyBounded = not ( sum ( intRel, SequentFormulasGenerator.sequent (),
         * not ( add ( applyTF ( intRel, tf.intRelation ), InEquationMultFeature .partiallyBounded (
         * instOf ( "multLeft" ), instOf ( "multFacLeft" ), sub ( intRel, 0 ) ) ) ) ) );
         */

        final Feature totallyBounded = not(sum(intRel, SequentFormulasGenerator.sequent(),
            not(add(applyTF(intRel, tf.intRelation), InEquationMultFeature
                    .totallyBounded(instOf("multLeft"), instOf("multFacLeft"), sub(intRel, 0))))));

        final Feature exactlyBounded = not(sum(intRel, SequentFormulasGenerator.sequent(),
            not(add(applyTF(intRel, tf.intRelation), InEquationMultFeature
                    .exactlyBounded(instOf("multLeft"), instOf("multFacLeft"), sub(intRel, 0))))));

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
        bindRuleSet(d, "inEqSimp_nonLin_multiply", add(applyTF("multLeft", tf.nonNegMonomial),
            applyTF("multRight", tf.polynomial),
            ifZero(MatchedIfFeature.INSTANCE,
                SumFeature.createSum(applyTF("multFacLeft", tf.nonNegMonomial),
                    ifZero(applyTF("multRight", tf.literal), longConst(-100)),
                    ifZero(applyTF("multFacRight", tf.literal), longConst(-100),
                        applyTF("multFacRight", tf.polynomial)),
                    /*
                     * ifZero ( applyTF ( "multRight", tf.literal ), longConst ( -100 ), applyTF (
                     * "multRight", tf.polynomial ) ), ifZero ( applyTF ( "multFacRight", tf.literal
                     * ), longConst ( -100 ), applyTF ( "multFacRight", tf.polynomial ) ),
                     */
                    not(TermSmallerThanFeature.create(FocusProjection.create(0),
                        AssumptionProjection.create(0))),
                    ifZero(exactlyBounded, longConst(0),
                        ifZero(totallyBounded, longConst(100), notAllowedF))
                /*
                 * ifZero ( partiallyBounded, longConst ( 400 ), notAllowedF ) ) ),
                 */
                /*
                 * applyTF ( "multLeft", rec ( tf.mulF, longTermConst ( 20 ) ) ), applyTF (
                 * "multFacLeft", rec ( tf.mulF, longTermConst ( 20 ) ) ), applyTF ( "multRight",
                 * rec ( tf.addF, longTermConst ( 4 ) ) ), applyTF ( "multFacRight", rec ( tf.addF,
                 * longTermConst ( 4 ) ) ),
                 */
                ), notAllowedF)));
    }

    private void setupInEqSimpInstantiation(RuleSetDispatchFeature d) {
        // category "handling of non-linear inequations"

        setupSquaresAreNonNegative(d);

        if (arithNonLinInferences()) {
            setupInEqCaseDistinctions(d);
        }
    }

    // For taclets that need instantiation, but where the instantiation is
    // deterministic and does not have to be repeated at a later point, we
    // setup the same feature terms as in the instantiation method. The
    // definitions in <code>setupInstantiationWithoutRetry</code> should
    // give cost infinity to those incomplete rule applications that will
    // never be instantiated (so that these applications can be removed from
    // the queue and do not have to be considered again).
    private void setupInEqSimpInstantiationWithoutRetry(RuleSetDispatchFeature d) {
        // category "direct inequations"

        setupPullOutGcd(d, "inEqSimp_pullOutGcd_leq", false);
        setupPullOutGcd(d, "inEqSimp_pullOutGcd_geq", true);

        // more efficient (but not confluent) versions for the antecedent
        bindRuleSet(d, "inEqSimp_pullOutGcd_antec", -10);

        // category "handling of non-linear inequations"

        final TermBuffer divisor = new TermBuffer();
        final TermBuffer dividend = new TermBuffer();

        bindRuleSet(d, "inEqSimp_nonLin_divide", SumFeature.createSum(
            applyTF("divProd", tf.nonCoeffMonomial),
            applyTFNonStrict("divProdBoundNonPos", tf.nonPosLiteral),
            applyTFNonStrict("divProdBoundNonNeg", tf.nonNegLiteral),
            ifZero(MatchedIfFeature.INSTANCE,
                let(divisor, instOf("divX"), let(dividend, instOf("divProd"),
                    SumFeature.createSum(applyTF(divisor, tf.nonCoeffMonomial),
                        not(eq(dividend, divisor)), applyTFNonStrict("divXBoundPos", tf.posLiteral),
                        applyTFNonStrict("divXBoundNeg", tf.negLiteral),
                        ReducibleMonomialsFeature.createReducible(dividend, divisor), instantiate(
                            "divY", ReduceMonomialsProjection.create(dividend, divisor))))))));

        setupNonLinTermIsPosNeg(d, "inEqSimp_nonLin_pos", true);
        setupNonLinTermIsPosNeg(d, "inEqSimp_nonLin_neg", false);
    }

    private void setupNonLinTermIsPosNeg(RuleSetDispatchFeature d, String ruleSet, boolean pos) {
        final TermBuffer divisor = new TermBuffer();
        final TermBuffer dividend = new TermBuffer();
        final TermBuffer quotient = new TermBuffer();
        final TermBuffer antecFor = new TermBuffer();

        bindRuleSet(d, ruleSet,
            SumFeature
                    .createSum(applyTF("divProd", tf.nonCoeffMonomial),
                        applyTFNonStrict("divProdBoundPos", tf.posLiteral),
                        applyTFNonStrict("divProdBoundNeg", tf.negLiteral),
                        ifZero(MatchedIfFeature.INSTANCE,
                            let(divisor, instOf("divX"), let(dividend, instOf("divProd"),
                                SumFeature.createSum(applyTF(divisor, tf.nonCoeffMonomial),
                                    not(applyTF(dividend, eq(divisor))),
                                    applyTFNonStrict("divXBoundNonPos", tf.nonPosLiteral),
                                    applyTFNonStrict("divXBoundNonNeg", tf.nonNegLiteral),
                                    ReducibleMonomialsFeature.createReducible(dividend, divisor),
                                    let(quotient,
                                        ReduceMonomialsProjection.create(dividend, divisor), add(
                                            sum(antecFor, SequentFormulasGenerator.antecedent(),
                                                not(applyTF(antecFor,
                                                    pos ? opSub(tf.geq, eq(quotient), tf.posLiteral)
                                                            : opSub(tf.leq, eq(quotient),
                                                                tf.negLiteral)))),
                                            instantiate("divY", quotient)))))))));
    }

    private void setupSquaresAreNonNegative(RuleSetDispatchFeature d) {
        final TermBuffer intRel = new TermBuffer();
        final TermBuffer product = new TermBuffer();
        final TermBuffer factor = new TermBuffer();

        final Feature productContainsSquare =
            applyTF(sub(product, 0), or(eq(factor), opSub(tf.mul, any(), eq(factor))));
        final Feature productIsProduct = applyTF(product, opSub(tf.mul, any(), not(tf.mulF)));

        bindRuleSet(d, "inEqSimp_nonNegSquares",
            forEach(intRel, SequentFormulasGenerator.sequent(),
                ifZero(applyTF(intRel, tf.intRelation),
                    forEach(product, SubtermGenerator.leftTraverse(sub(intRel, 0), tf.mulF),
                        ifZero(productIsProduct, let(factor, sub(product, 1),
                            ifZero(productContainsSquare, instantiate("squareFac", factor))))))));
    }

    private void setupInEqCaseDistinctions(RuleSetDispatchFeature d) {
        final TermBuffer intRel = new TermBuffer();
        final TermBuffer atom = new TermBuffer();
        final TermBuffer rootInf = new TermBuffer();

        final Feature posNegSplitting = forEach(intRel, SequentFormulasGenerator.antecedent(),
            add(applyTF(intRel, tf.intRelation),
                forEach(atom, SubtermGenerator.leftTraverse(sub(intRel, 0), tf.mulF),
                    SumFeature.createSum(applyTF(atom, add(tf.atom, not(tf.literal))),
                        allowPosNegCaseDistinction(atom), instantiate("signCasesLeft", atom),
                        longConst(IN_EQ_SIMP_NON_LIN_COST + 200)
                    // ,
                    // applyTF ( atom, rec ( any (),
                    // longTermConst ( 5 ) ) )
                    ))));

        bindRuleSet(d, "inEqSimp_signCases", posNegSplitting);

        final Feature strengthening = forEach(intRel, SequentFormulasGenerator.antecedent(),
            SumFeature.createSum(
                applyTF(intRel, add(or(tf.geqF, tf.leqF), sub(tf.atom, tf.literal))),
                instantiate("cutFormula", opTerm(tf.eq, sub(intRel, 0), sub(intRel, 1))),
                longConst(IN_EQ_SIMP_NON_LIN_COST + 300)
            // ,
            // applyTF ( sub ( intRel, 0 ),
            // rec ( any (), longTermConst ( 5 ) ) )
            ));

        final Feature rootInferences = forEach(intRel, SequentFormulasGenerator.antecedent(),
            add(isRootInferenceProducer(intRel),
                forEach(rootInf, RootsGenerator.create(intRel, getServices()),
                    add(instantiate("cutFormula", rootInf),
                        ifZero(applyTF(rootInf, op(Junctor.OR)), longConst(50)),
                        ifZero(applyTF(rootInf, op(Junctor.AND)), longConst(20)))),
                longConst(IN_EQ_SIMP_NON_LIN_COST)));

        bindRuleSet(d, "cut", oneOf(new Feature[] { strengthening, rootInferences }));
    }

    private Feature isRootInferenceProducer(TermBuffer intRel) {
        return applyTF(intRel, add(tf.intRelation, sub(tf.nonCoeffMonomial, tf.literal)));
    }

    private Feature allowPosNegCaseDistinction(TermBuffer atom) {
        final TermBuffer antecFor = new TermBuffer();
        final TermFeature eqAtom = eq(atom);

        return add(not(succIntEquationExists()),
            sum(antecFor, SequentFormulasGenerator.antecedent(),
                not(applyTF(antecFor, or(opSub(tf.eq, eqAtom, any()),
                    opSub(tf.leq, eqAtom, tf.negLiteral), opSub(tf.geq, eqAtom, tf.posLiteral))))));
    }

    private Feature allowInEqStrengthening(TermBuffer atom, TermBuffer literal) {
        final TermBuffer antecFor = new TermBuffer();

        return add(not(succIntEquationExists()),
            not(sum(antecFor, SequentFormulasGenerator.antecedent(),
                not(applyTF(antecFor, add(or(tf.leqF, tf.geqF), sub(eq(atom), eq(literal))))))));
    }

    private Feature succIntEquationExists() {
        final TermBuffer succFor = new TermBuffer();

        return not(sum(succFor, SequentFormulasGenerator.succedent(),
            not(applyTF(succFor, tf.intEquation))));
    }

    protected final Services getServices() {
        return getProof().getServices();
    }

    private void setupInEqCaseDistinctionsApproval(RuleSetDispatchFeature d) {
        final TermBuffer atom = new TermBuffer();
        final TermBuffer literal = new TermBuffer();
        final TermBuffer intRel = new TermBuffer();
        final TermBuffer rootInf = new TermBuffer();

        bindRuleSet(d, "inEqSimp_signCases", add(isInstantiated("signCasesLeft"),
            let(atom, instOf("signCasesLeft"), allowPosNegCaseDistinction(atom))));

        // this is somewhat ugly. we should introduce some concept of "tagging"
        // rule application so that they can be recognised again later
        bindRuleSet(d, "cut",
            add(isInstantiated("cutFormula"), or(
                not(sum(intRel, SequentFormulasGenerator.antecedent(),
                    ifZero(isRootInferenceProducer(intRel),
                        sum(rootInf, RootsGenerator.create(intRel, getServices()),
                            not(eq(instOf("cutFormula"), rootInf)))))),
                ifZero(applyTF("cutFormula", opSub(tf.eq, tf.atom, tf.literal)),
                    let(atom, sub(instOf("cutFormula"), 0), let(literal,
                        sub(instOf("cutFormula"), 1), allowInEqStrengthening(atom, literal)))))));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Axiomatisation and algorithms for further arithmetic operations:
    // division, modulus, modular Java operations
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private void setupDefOpsPrimaryCategories(RuleSetDispatchFeature d) {

        if (arithDefOps()) {
            // the axiom defining division only has to be inserted once, because
            // it adds equations to the antecedent
            bindRuleSet(d, "defOps_div",
                SumFeature.createSum(NonDuplicateAppModPositionFeature.INSTANCE,
                    applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                    applyTF("divNum", tf.notContainsDivMod),
                    applyTF("divDenom", tf.notContainsDivMod),
                    ifZero(isBelow(ff.modalOperator), longConst(200))));

            bindRuleSet(d, "defOps_jdiv",
                SumFeature.createSum(NonDuplicateAppModPositionFeature.INSTANCE,
                    applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                    applyTF("divNum", tf.notContainsDivMod),
                    applyTF("divDenom", tf.notContainsDivMod),
                    ifZero(isBelow(ff.modalOperator), longConst(200))));

            bindRuleSet(d, "defOps_jdiv_inline", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.polynomial), longConst(-5000)));

            setupDefOpsExpandMod(d);

            bindRuleSet(d, "defOps_expandRanges", -8000);
            bindRuleSet(d, "defOps_expandJNumericOp", -500);
            bindRuleSet(d, "defOps_modHomoEq", -5000);
        } else {
            bindRuleSet(d, "defOps_div", inftyConst());
            bindRuleSet(d, "defOps_jdiv", inftyConst());

            bindRuleSet(d, "defOps_jdiv_inline", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.literal), longConst(-4000)));

            bindRuleSet(d, "defOps_mod", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.literal), longConst(-4000)));

            bindRuleSet(d, "defOps_expandRanges", inftyConst());
            bindRuleSet(d, "defOps_expandJNumericOp", inftyConst());
            bindRuleSet(d, "defOps_modHomoEq", inftyConst());
        }

    }

    private void setupDefOpsExpandMod(RuleSetDispatchFeature d) {
        final TermBuffer superTerm = new TermBuffer();

        final Feature subsumedModulus =
            add(applyTF(superTerm, sub(opSub(tf.mod, any(), tf.literal), tf.zeroLiteral)),
                PolynomialValuesCmpFeature.divides(instOf("divDenom"), sub(sub(superTerm, 0), 1)));

        final Feature exSubsumedModulus = add(applyTF("divDenom", tf.literal), not(sum(superTerm,
            SuperTermGenerator.upwardsWithIndex(sub(or(tf.addF, tf.mulF), any()), getServices()),
            not(subsumedModulus))));

        bindRuleSet(d, "defOps_mod",
            ifZero(add(applyTF("divNum", tf.literal), applyTF("divDenom", tf.literal)),
                longConst(-4000),
                SumFeature.createSum(applyTF("divNum", tf.polynomial),
                    applyTF("divDenom", tf.polynomial),
                    ifZero(isBelow(ff.modalOperator), exSubsumedModulus,
                        or(add(applyTF("divNum", tf.notContainsDivMod),
                            applyTF("divDenom", tf.notContainsDivMod)), exSubsumedModulus)),
                    longConst(-3500))));
    }

    private Feature isBelow(TermFeature t) {
        final TermBuffer superTerm = new TermBuffer();
        return not(sum(superTerm, SuperTermGenerator.upwards(any(), getServices()),
            not(applyTF(superTerm, t))));
    }

    private void setupDivModDivision(RuleSetDispatchFeature d) {

        final TermBuffer denomLC = new TermBuffer();
        final TermBuffer numTerm = new TermBuffer();
        final TermBuffer divCoeff = new TermBuffer();

        // exact polynomial division

        final Feature checkNumTerm = ifZero(
            add(not(applyTF(numTerm, tf.addF)),
                ReducibleMonomialsFeature.createReducible(numTerm, denomLC)),
            add(instantiate("polyDivCoeff", ReduceMonomialsProjection.create(numTerm, denomLC)),
                inftyConst()));

        final Feature isReduciblePoly =
            sum(numTerm, SubtermGenerator.rightTraverse(instOf("divNum"), tf.addF), checkNumTerm);

        // polynomial division modulo equations of the antecedent

        final Feature checkCoeffE = ifZero(contains(divCoeff, FocusProjection.create(0)),
            // do not apply if the result contains the original term
            longConst(0), add(instantiate("polyDivCoeff", divCoeff), inftyConst()));

        final Feature isReduciblePolyE =
            sum(numTerm, SubtermGenerator.rightTraverse(instOf("divNum"), tf.addF),
                ifZero(applyTF(numTerm, tf.addF), longConst(0), sum(divCoeff,
                    MultiplesModEquationsGenerator.create(numTerm, denomLC), checkCoeffE)));

        bindRuleSet(d, "defOps_divModPullOut",
            SumFeature.createSum(
                not(add(applyTF("divNum", tf.literal), applyTF("divDenom", tf.literal))),
                applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                ifZero(applyTF("divDenom", tf.addF),
                    let(denomLC, sub(instOf("divDenom"), 1), not(isReduciblePoly)),
                    let(denomLC, instOf("divDenom"), ifZero(isReduciblePoly,
                        // no possible division
                        // has been found so far
                        add(NotInScopeOfModalityFeature.INSTANCE, ifZero(isReduciblePolyE,
                            // try again
                            // later
                            longConst(-POLY_DIVISION_COST)))))),
                longConst(100)));

    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the approval of complete taclet applications
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected Feature setupApprovalF() {
        final Feature depSpecF;
        final String depProp = strategyProperties.getProperty(StrategyProperties.DEP_OPTIONS_KEY);
        final SetRuleFilter depFilter = new SetRuleFilter();
        depFilter.addRuleToSet(UseDependencyContractRule.INSTANCE);
        if (depProp.equals(StrategyProperties.DEP_ON)) {
            depSpecF = ConditionalFeature.createConditional(depFilter,
                ifZero(new DependencyContractFeature(), longConst(250), inftyConst()));
        } else {
            depSpecF = ConditionalFeature.createConditional(depFilter, inftyConst());
        }

        return add(NonDuplicateAppFeature.INSTANCE, depSpecF);
    }

    private RuleSetDispatchFeature setupApprovalDispatcher() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        final IntegerLDT numbers = getServices().getTypeConverter().getIntegerLDT();

        if (arithNonLinInferences()) {
            setupMultiplyInequations(d, inftyConst());
        }

        // these taclets are not supposed to be applied with metavariable
        // instantiations
        // I'll keep it here for the moment as documentation, but comment it out
        // as meta variables are no longer part of KeY 2.x
        /*
         * bindRuleSet ( d, "inEqSimp_pullOutGcd", isInstantiated ( "elimGcd" ) ); bindRuleSet ( d,
         * "polySimp_pullOutGcd", isInstantiated ( "elimGcd" ) );
         *
         * bindRuleSet ( d, "inEqSimp_nonNegSquares", isInstantiated ( "squareFac" ) ); bindRuleSet
         * ( d, "inEqSimp_nonLin_divide", isInstantiated ( "divY" ) ); bindRuleSet ( d,
         * "inEqSimp_nonLin_pos", isInstantiated ( "divY" ) ); bindRuleSet ( d,
         * "inEqSimp_nonLin_neg", isInstantiated ( "divY" ) );
         *
         * bindRuleSet ( d, "inEqSimp_signCases", isInstantiated ( "signCasesLeft" ) );
         */

        setupNewSymApproval(d, numbers);

        bindRuleSet(d, "defOps_div", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "defOps_jdiv", NonDuplicateAppModPositionFeature.INSTANCE);

        if (arithNonLinInferences()) {
            setupInEqCaseDistinctionsApproval(d);
        }

        bindRuleSet(d, "inReachableStateImplication", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "limitObserver", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "partialInvAxiom", NonDuplicateAppModPositionFeature.INSTANCE);

        setupClassAxiomApproval(d);
        setupQuantifierInstantiationApproval(d);
        setupSplittingApproval(d);

        bindRuleSet(d, "apply_select_eq",
            add(isInstantiated("s"), isInstantiated("t1"),
                or(applyTF("s", rec(any(), SimplifiedSelectTermFeature.create(heapLDT))),
                    add(NoSelfApplicationFeature.INSTANCE,
                        applyTF("t1", IsSelectSkolemConstantTermFeature.INSTANCE)))));
        bindRuleSet(d, "apply_auxiliary_eq",
            add(NoSelfApplicationFeature.INSTANCE, isInstantiated("s"),
                applyTF("s",
                    rec(any(),
                        add(SimplifiedSelectTermFeature.create(heapLDT), not(ff.ifThenElse)))),
                not(ContainsTermFeature.create(instOf("s"), instOf("t1")))));

        // Without EqNonDuplicateAppFeature.INSTANCE
        // rule 'applyEq' might be applied on the same term
        // without changing the sequent for a really long time. This is tested by
        // TestSymbolicExecutionTreeBuilder#testInstanceOfNotInEndlessLoop()
        bindRuleSet(d, "apply_equations", EqNonDuplicateAppFeature.INSTANCE);

        return d;
    }

    private void setupClassAxiomApproval(final RuleSetDispatchFeature d) {
        // isInstantiated approves also when sv_heap does not occur
        if (classAxiomApplicationEnabled()) {
            TermBuffer tb = new TermBuffer();
            final Feature needsInstantiation = SVNeedsInstantiation.create("sv_heap");
            /*
             * if 'sv_heap' is present and instantiated, allow application only if the heap used to
             * instantiate 'sv_heap' still occurs in the sequent. Otherwise this was a rather short
             * lived heap term which has been rewritten since. Hence, we discard it to avoid too
             * many most likely useless applications.
             */
            final Feature approveInst = ifZero(isInstantiated("sv_heap"),
                /*
                 * the sum expression is 0 if the heap does not occur and infinite if it does occur,
                 * the outer 'not' then ensures that the costs are infinite in the first and 0 in
                 * the latter case
                 */
                not(sum(tb, HeapGenerator.INSTANCE, not(eq(instOf("sv_heap"), tb)))));

            if (classAxiomDelayedApplication()) {
                bindRuleSet(d, "classAxiom", add(sequentContainsNoPrograms(),
                    /*
                     * can be applied if sv_heap is instantiated or not present
                     */
                    not(needsInstantiation), approveInst, NonDuplicateAppFeature.INSTANCE));
            } else {
                bindRuleSet(d, "classAxiom", add(
                    /*
                     * can be applied if sv_heap is instantiated or not present
                     */
                    not(needsInstantiation), approveInst, NonDuplicateAppFeature.INSTANCE));
            }
        } else {
            bindRuleSet(d, "classAxiom", inftyConst());
        }
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Feature terms that handle the instantiation of incomplete taclet
    // applications
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    private RuleSetDispatchFeature setupInstantiationF() {
        enableInstantiate();

        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        setupQuantifierInstantiation(d);

        setupArithPrimaryCategories(d);
        setupDefOpsPrimaryCategories(d);

        setupInstantiationWithoutRetry(d);

        setupInEqSimpInstantiation(d);

        setClassAxiomInstantiation(d);

        disableInstantiate();
        return d;
    }

    private void setClassAxiomInstantiation(final RuleSetDispatchFeature d) {
        // class axioms
        final TermBuffer heapVar = new TermBuffer();
        final Feature needsInstantiation = SVNeedsInstantiation.create("sv_heap");

        final Feature heapInstantiator = ifZero(needsInstantiation,
            forEach(heapVar, HeapGenerator.INSTANCE_EXCLUDE_UPDATES,
                add(instantiate("sv_heap", heapVar),
                    // prefer simpler heap terms before more
                    // complicated ones
                    applyTF(heapVar, rec(not(tf.atom), longTermConst(10))))),
            longConst(0));

        bindRuleSet(d, "classAxiom", heapInstantiator);
    }

    /**
     * For taclets that need instantiation, but where the instantiation is deterministic and does
     * not have to be repeated at a later point, we setup the same feature terms both in the cost
     * computation method and in the instantiation method. The definitions in
     * <code>setupInstantiationWithoutRetry</code> should give cost infinity to those incomplete
     * rule applications that will never be instantiated (so that these applications can be removed
     * from the queue and do not have to be considered again).
     */
    private void setupInstantiationWithoutRetry(RuleSetDispatchFeature d) {
        setupPolySimpInstantiationWithoutRetry(d);
        setupInEqSimpInstantiationWithoutRetry(d);
    }

    @Override
    public Name name() {
        return new Name(JAVA_CARD_DL_STRATEGY);
    }

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     *
     * @param app rule application
     * @param pio corresponding {@link PosInOccurrence}
     * @param goal corresponding goal
     * @return the cost of the rule application expressed as a <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule shall not be applied at
     *         all (it is discarded by the strategy).
     */
    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {
        var time = System.nanoTime();
        try {
            return costComputationF.computeCost(app, pio, goal);
        } finally {
            PERF_COMPUTE.addAndGet(System.nanoTime() - time);
        }
    }

    /**
     * Re-Evaluate a <code>RuleApp</code>. This method is called immediately before a rule is really
     * applied
     *
     * @param app the rule application
     * @param pio the position in occurrence
     * @param goal the goal
     * @return true iff the rule should be applied, false otherwise
     */
    @Override
    public final boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        var time = System.nanoTime();
        try {
            return !(approvalF.computeCost(app, pio, goal) == TopRuleAppCost.INSTANCE);
        } finally {
            PERF_APPROVE.addAndGet(System.nanoTime() - time);
        }
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        var time = System.nanoTime();
        try {
            return instantiationF.computeCost(app, pio, goal);
        } finally {
            PERF_INSTANTIATE.addAndGet(System.nanoTime() - time);
        }
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Termfeatures: characterisations of terms and formulas
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                .equals(StrategyProperties.STOPMODE_NONCLOSE);
    }
}
