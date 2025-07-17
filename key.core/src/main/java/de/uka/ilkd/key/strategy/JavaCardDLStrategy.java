/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.feature.findprefix.FindPrefixRestrictionFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.ClausesSmallerThanFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EliminableQuantifierTF;
import de.uka.ilkd.key.strategy.quantifierHeuristics.HeuristicInstantiation;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCost;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCostScalerFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.SplittableQuantifiedFormulaFeature;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.*;
import de.uka.ilkd.key.strategy.termgenerator.AllowedCutPositionsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.HeapGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;
import de.uka.ilkd.key.strategy.termgenerator.TriggeredInstantiations;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.proof.rulefilter.SetRuleFilter;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.feature.instantiator.ChoicePoint;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termfeature.IsNonRigidTermFeature;
import org.key_project.prover.strategy.costbased.termfeature.OperatorClassTF;

import org.jspecify.annotations.NonNull;

/**
 * Strategy tailored to be used as long as a java program can be found in the sequent.
 */
public class JavaCardDLStrategy extends AbstractFeatureStrategy {
    public static final AtomicLong PERF_COMPUTE = new AtomicLong();
    public static final AtomicLong PERF_APPROVE = new AtomicLong();
    public static final AtomicLong PERF_INSTANTIATE = new AtomicLong();

    public static final String JAVA_CARD_DL_STRATEGY = "JavaCardDLStrategy";

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

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null || instantiationDispatcher.get(rs) != null
                || approvalDispatcher.get(rs) != null;
    }

    protected Feature setupGlobalF(Feature dispatcher) {

        final Feature methodSpecF;
        final String methProp =
            strategyProperties.getProperty(StrategyProperties.METHOD_OPTIONS_KEY);
        switch (methProp) {
        case StrategyProperties.METHOD_CONTRACT -> methodSpecF = methodSpecFeature(longConst(-20));
        case StrategyProperties.METHOD_EXPAND, StrategyProperties.METHOD_NONE -> methodSpecF =
            methodSpecFeature(inftyConst());
        default -> {
            methodSpecF = null;
            assert false;
        }
        }

        final String queryProp =
            strategyProperties.getProperty(StrategyProperties.QUERY_OPTIONS_KEY);
        final Feature queryF;
        switch (queryProp) {
        case StrategyProperties.QUERY_ON -> queryF =
            querySpecFeature(new QueryExpandCost(200, 1, 1, false));
        case StrategyProperties.QUERY_RESTRICTED ->
            // All tests in the example directory pass with this strategy.
            // Hence, the old query_on strategy is obsolete.
            queryF = querySpecFeature(new QueryExpandCost(500, 0, 1, true));
        case StrategyProperties.QUERY_OFF -> queryF = querySpecFeature(inftyConst());
        default -> {
            queryF = null;
            assert false;
        }
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

        final Feature oneStepSimplificationF =
            oneStepSimplificationFeature(longConst(-11000));

        final Feature mergeRuleF;
        final String mpsProperty =
            strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);
        if (mpsProperty.equals(StrategyProperties.MPS_MERGE)) {
            mergeRuleF = mergeRuleFeature(longConst(-4000));
        } else {
            mergeRuleF = mergeRuleFeature(inftyConst());
        }

        // final Feature smtF = smtFeature(inftyConst());

        return SumFeature.createSum(
            // splitF,
            // strengthenConstraints,
            oneStepSimplificationF, mergeRuleF,
            // smtF,
            methodSpecF, queryF, depSpecF, loopInvF, blockFeature, loopBlockFeature,
            loopBlockApplyHeadFeature, dispatcher);
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
        final LocSetLDT locSetLDT = getServices().getTypeConverter().getLocSetLDT();
        final IntegerLDT numbers = getServices().getTypeConverter().getIntegerLDT();

        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "semantics_blasting", inftyConst());
        bindRuleSet(d, "simplify_heap_high_costs", inftyConst());

        bindRuleSet(d, "closure", -15000);
        bindRuleSet(d, "alpha", -7000);
        bindRuleSet(d, "delta", -6000);
        bindRuleSet(d, "simplify_boolean", -200);

        final Feature findDepthFeature =
            FindDepthFeature.getInstance();

        bindRuleSet(d, "concrete",
            add(longConst(-11000),
                ScaleFeature.createScaled(findDepthFeature, 10.0)));
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
            ifZero(MatchedAssumesFeature.INSTANCE, NoSelfApplicationFeature.INSTANCE));

        bindRuleSet(d, "find_term_not_in_assumes", ifZero(MatchedAssumesFeature.INSTANCE,
            not(contains(AssumptionProjection.create(0), FocusProjection.INSTANCE))));

        bindRuleSet(d, "update_elim",
            add(longConst(-8000), ScaleFeature.createScaled(findDepthFeature, 10.0)));
        bindRuleSet(d, "update_apply_on_update",
            add(longConst(-7000), ScaleFeature.createScaled(findDepthFeature, 10.0)));
        bindRuleSet(d, "update_join", -4600);
        bindRuleSet(d, "update_apply", -4500);

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
            ifZero(MatchedAssumesFeature.INSTANCE, DiffFindAndIfFeature.INSTANCE));

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

        final String[] exceptionsWithPenalty = { "java.lang.NullPointerException",
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
        case StrategyProperties.METHOD_CONTRACT ->
            /*
             * If method treatment by contracts is chosen, this does not mean that method expansion
             * is disabled. The original cost was 200 and is now increased to 2000 in order to
             * repress method expansion stronger when method treatment by contracts is chosen.
             */
            bindRuleSet(d, "method_expand", longConst(2000));
        case StrategyProperties.METHOD_EXPAND -> bindRuleSet(d, "method_expand", longConst(100));
        case StrategyProperties.METHOD_NONE -> bindRuleSet(d, "method_expand", inftyConst());
        default -> throw new RuntimeException("Unexpected strategy property " + methProp);
        }

        final String mpsProp = strategyProperties.getProperty(StrategyProperties.MPS_OPTIONS_KEY);

        switch (mpsProp) {
        case StrategyProperties.MPS_MERGE ->
            /*
             * For this case, we use a special feature, since deleting merge points should only be
             * done after a merge rule application.
             */
            bindRuleSet(d, "merge_point", DeleteMergePointRuleFeature.INSTANCE);
        case StrategyProperties.MPS_SKIP -> bindRuleSet(d, "merge_point", longConst(-5000));
        case StrategyProperties.MPS_NONE -> bindRuleSet(d, "merge_point", inftyConst());
        default -> throw new RuntimeException("Unexpected strategy property " + methProp);
        }


        final String queryAxProp =
            strategyProperties.getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
        switch (queryAxProp) {
        case StrategyProperties.QUERYAXIOM_ON -> bindRuleSet(d, "query_axiom", longConst(-3000));
        case StrategyProperties.QUERYAXIOM_OFF -> bindRuleSet(d, "query_axiom", inftyConst());
        default -> throw new RuntimeException("Unexpected strategy property " + queryAxProp);
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
                not(or(PrimitiveHeapTermFeature.create(heapLDT), anonHeapTermFeature()))),
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
            add(isSelectSkolemConstantTerm("sk"),
                applyTF(sub(FocusProjection.INSTANCE, 0),
                    not(SimplifiedSelectTermFeature.create(heapLDT))),
                longConst(-5600)));
        bindRuleSet(d, "apply_auxiliary_eq",
            // replace skolem constant by it's computed value
            add(isSelectSkolemConstantTerm("t1"), longConst(-5500)));
        bindRuleSet(d, "hide_auxiliary_eq",
            // hide auxiliary equation after the skolem constants have
            // been replaced by it's computed value
            add(isSelectSkolemConstantTerm("auxiliarySK"),
                applyTF("result",
                    rec(any(),
                        add(SimplifiedSelectTermFeature.create(heapLDT), not(ff.ifThenElse)))),
                not(ContainsTermFeature.create(instOf("result"), instOf("auxiliarySK"))),
                longConst(-5400)));
        bindRuleSet(d, "hide_auxiliary_eq_const",
            // hide auxiliary equation after the skolem constatns have
            // been replaced by it's computed value
            add(isSelectSkolemConstantTerm("auxiliarySK"), longConst(-500)));
    }

    private void setupReplaceKnown(RuleSetDispatchFeature d) {
        final Feature commonF =
            add(ifZero(MatchedAssumesFeature.INSTANCE, DiffFindAndIfFeature.INSTANCE),
                longConst(-5000),
                add(DiffFindAndReplacewithFeature.INSTANCE,
                    ScaleFeature.createScaled(CountMaxDPathFeature.INSTANCE, 10.0)));

        bindRuleSet(d, "replace_known_left", commonF);

        bindRuleSet(d, "replace_known_right",
            add(commonF, ifZero(directlyBelowSymbolAtIndex(Junctor.IMP, 1), longConst(100),
                ifZero(directlyBelowSymbolAtIndex(Equality.EQV, -1), longConst(100)))));
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
            ifZero(MatchedAssumesFeature.INSTANCE, add(applyTF("negLit", tf.negLiteral),
                applyTFNonStrict("nonNegLit", tf.nonNegLiteral))));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Queries for the active taclet options
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

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

    private Feature allowSplitting(ProjectionToTerm<Goal> focus) {
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
        final ProjectionToTerm<Goal> splitCondition = sub(FocusProjection.INSTANCE, 0);
        bindRuleSet(d, "split_cond", add(// do not split over formulas containing auxiliary
            // variables
            applyTF(FocusProjection.INSTANCE,
                rec(any(), not(selectSkolemConstantTermFeature()))),
            // prefer splits when condition has quantifiers (less
            // likely to be simplified away)
            applyTF(splitCondition,
                rec(ff.quantifiedFor, ifZero(ff.quantifiedFor, longTermConst(-10)))),
            FindDepthFeature.getInstance(), // prefer top level splits
            ScaleFeature.createAffine(countOccurrences(splitCondition), -10, 10),
            sum(superF, SuperTermGenerator.upwards(any(), getServices()),
                applyTF(superF, not(ff.elemUpdate))),
            ifZero(applyTF(FocusProjection.INSTANCE, ContainsExecutableCodeTermFeature.PROGRAMS),
                longConst(-100), longConst(25))));
        ProjectionToTerm<Goal> cutFormula = instOf("cutFormula");
        Feature countOccurrencesInSeq =
            ScaleFeature.createAffine(countOccurrences(cutFormula), -10, 10);
        bindRuleSet(d, "cut_direct",
            SumFeature
                    .createSum(
                        not(TopLevelFindFeature.ANTEC_OR_SUCC_WITH_UPDATE),
                        AllowedCutPositionFeature.INSTANCE,
                        ifZero(notBelowQuantifier(),
                            add(
                                applyTF(cutFormula, add(ff.cutAllowed,
                                    // do not cut over formulas containing
                                    // auxiliary variables
                                    rec(any(), not(selectSkolemConstantTermFeature())))),
                                // prefer cuts over "something = null"
                                ifZero(applyTF(FocusProjection.INSTANCE,
                                    opSub(tf.eq, any(), vf.nullTerm)),
                                    longConst(-5), longConst(0)),
                                // punish cuts over formulas containing anon heap functions
                                ifZero(applyTF(cutFormula, rec(any(), not(anonHeapTermFeature()))),
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
            ifZero(notBelowQuantifier(), noBetterCut)));
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
                ifZero(MatchedAssumesFeature.INSTANCE,
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

        bindRuleSet(d, "int_apply_equations",
            SumFeature.createSum(ifZero(applyTF(FocusProjection.create(0), tf.intF),
                add(applyTF(FocusProjection.create(0), tf.monomial),
                    ScaleFeature.createScaled(FindRightishFeature.create(numbers), 5.0)),
                inftyConst()),
                ifZero(MatchedAssumesFeature.INSTANCE,
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
                                    inftyConst()))))))),
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

        bindRuleSet(d, "negationNormalForm", add(BelowBinderFeature.getInstance(),
            longConst(-500),
            ScaleFeature.createScaled(FindDepthFeature.<Goal>getInstance(), 10.0)));

        bindRuleSet(d, "moveQuantToLeft",
            add(quantifiersMightSplit() ? longConst(0)
                    : applyTF(FocusFormulaProjection.INSTANCE, ff.quantifiedPureLitConjDisj),
                longConst(-550)));

        bindRuleSet(d, "conjNormalForm",
            ifZero(
                add(or(FocusInAntecFeature.getInstance(), notBelowQuantifier()),
                    NotInScopeOfModalityFeature.INSTANCE),
                add(longConst(-150),
                    ScaleFeature.createScaled(FindDepthFeature.<Goal>getInstance(), 20)),
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
                applyTF(FocusProjection.INSTANCE,
                    add(ff.quantifiedClauseSet, not(opSub(Quantifier.ALL, ff.orF)),
                        EliminableQuantifierTF.INSTANCE)),
                SumFeature.createSum(onlyInScopeOfQuantifiers(),
                    SplittableQuantifiedFormulaFeature.INSTANCE,
                    ifZero(FocusInAntecFeature.getInstance(),
                        applyTF(FocusProjection.INSTANCE, sub(ff.andF)),
                        applyTF(FocusProjection.INSTANCE, sub(ff.orF))))),
                longConst(-300)));

        bindRuleSet(d, "swapQuantifiers",
            add(applyTF(FocusProjection.INSTANCE, add(ff.quantifiedClauseSet,
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
                // otherwise, sorting is not likely to have any big effect
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

        final Feature belowUnskolemisableQuantifier =
            ifZero(FocusInAntecFeature.getInstance(),
                not(sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                    not(applyTF(superFor, op(Quantifier.ALL))))),
                not(sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                    not(applyTF(superFor, op(Quantifier.EX))))));

        bindRuleSet(d, "cnf_expandIfThenElse", add(
            isBelow(OperatorClassTF.create(Quantifier.class)),
            onlyBelowQuanAndOr, belowUnskolemisableQuantifier));

        final Feature pullOutQuantifierAllowed =
            add(isBelow(OperatorClassTF.create(Quantifier.class)), onlyBelowQuanAndOr, applyTF(
                FocusProjection.create(0), sub(ff.quantifiedClauseSet, ff.quantifiedClauseSet)));

        bindRuleSet(d, "pullOutQuantifierUnifying", -20);

        bindRuleSet(d, "pullOutQuantifierAll", add(pullOutQuantifierAllowed,
            ifZero(FocusInAntecFeature.getInstance(), longConst(-20), longConst(-40))));

        bindRuleSet(d, "pullOutQuantifierEx", add(pullOutQuantifierAllowed,
            ifZero(FocusInAntecFeature.getInstance(), longConst(-40), longConst(-20))));
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
                SumFeature.createSum(FocusInAntecFeature.getInstance(),
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


    protected final Feature onlyInScopeOfQuantifiers() {
        final TermBuffer buf = new TermBuffer();
        return sum(buf, SuperTermGenerator.upwards(any(), getServices()),
            applyTF(buf, ff.quantifiedFor));
    }

    protected Feature notBelowQuantifier() {
        final TermBuffer superFor = new TermBuffer();
        return or(TopLevelFindFeature.ANTEC_OR_SUCC,
            sum(superFor, SuperTermGenerator.upwards(any(), getServices()),
                not(applyTF(superFor, OperatorClassTF.create(Quantifier.class)))));
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

        bindRuleSet(d, "inReachableStateImplication", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "limitObserver", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "partialInvAxiom", NonDuplicateAppModPositionFeature.INSTANCE);

        setupClassAxiomApproval(d);
        setupQuantifierInstantiationApproval(d);
        setupSplittingApproval(d);

        bindRuleSet(d, "apply_select_eq",
            add(isInstantiated("s"), isInstantiated("t1"),
                or(applyTF("s", rec(any(), SimplifiedSelectTermFeature.create(heapLDT))),
                    add(NoSelfApplicationFeature.INSTANCE, isSelectSkolemConstantTerm("t1")))));
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
             * instantiate 'sv_heap' still occurs in the sequent. Otherwise, this was a rather
             * short-lived heap term which has been rewritten since. Hence, we discard it to avoid
             * too many most likely useless applications.
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


    @Override
    public @NonNull Name name() {
        return new Name(JAVA_CARD_DL_STRATEGY);
    }

    /**
     * Evaluate the cost of a <code>RuleApp</code>.
     *
     * @param app rule application
     * @param pio corresponding {@link PosInOccurrence}
     * @param goal corresponding goal
     * @param mState the {@link MutableState} to query for information like current value of
     *        {@link TermBuffer}s or
     *        {@link ChoicePoint}s
     * @return the cost of the rule application expressed as a <code>RuleAppCost</code> object.
     *         <code>TopRuleAppCost.INSTANCE</code> indicates that the rule shall not be applied at
     *         all (it is discarded by the strategy).
     */
    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pio,
            Goal goal,
            MutableState mState) {
        var time = System.nanoTime();
        try {
            return costComputationF.computeCost(app, pio, goal, mState);
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
    public final boolean isApprovedApp(RuleApp app,
            PosInOccurrence pio, Goal goal) {
        var time = System.nanoTime();
        try {
            return !(approvalF.computeCost(app, pio, goal,
                new MutableState()) == TopRuleAppCost.INSTANCE);
        } finally {
            PERF_APPROVE.addAndGet(System.nanoTime() - time);
        }
    }

    @Override
    protected RuleAppCost instantiateApp(RuleApp app,
            PosInOccurrence pio, Goal goal,
            MutableState mState) {
        var time = System.nanoTime();
        try {
            return instantiationF.computeCost(app, pio, goal, mState);
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
