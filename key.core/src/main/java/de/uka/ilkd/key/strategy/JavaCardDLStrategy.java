/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.concurrent.atomic.AtomicLong;

import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.UseDependencyContractRule;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.*;
import de.uka.ilkd.key.strategy.termgenerator.HeapGenerator;
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

import org.jspecify.annotations.NonNull;

/// This strategy is the catch-all for Java related features that are either
/// cross-cutting or one of the features that do not fit well into any other
/// strategy.
///
/// Do not create directly, instead use [JavaCardDLStrategyFactory].
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


    protected JavaCardDLStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);
        heapLDT = getServices().getTypeConverter().getHeapLDT();

        this.strategyProperties = (StrategyProperties) strategyProperties.clone();

        this.tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        this.ff = new FormulaTermFeatures(this.tf);

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

    protected Feature setupGlobalF(@NonNull Feature dispatcher) {
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

        final Feature oneStepSimplificationF =
            oneStepSimplificationFeature(longConst(-11000));

        // final Feature smtF = smtFeature(inftyConst());

        return SumFeature.createSum(
            // splitF,
            // strengthenConstraints,
            oneStepSimplificationF,
            // smtF,
            queryF, depSpecF, dispatcher);
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
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "semantics_blasting", inftyConst());
        bindRuleSet(d, "simplify_heap_high_costs", inftyConst());

        bindRuleSet(d, "javaIntegerSemantics",
            ifZero(sequentContainsNoPrograms(), longConst(-5000), ifZero(
                leq(CountBranchFeature.INSTANCE, longConst(1)), longConst(-5000), inftyConst())));

        setupSelectSimplification(d);

        bindRuleSet(d, "test_gen", inftyConst());
        bindRuleSet(d, "test_gen_empty_modality_hide", inftyConst());
        bindRuleSet(d, "test_gen_quan", inftyConst());
        bindRuleSet(d, "test_gen_quan_num", inftyConst());

        // This is moved here instead of FOLStrategy, because it deals only w/ loc sets
        if (!StrategyProperties.QUANTIFIERS_NONE
                .equals(
                    strategyProperties.getProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY))) {
            final LocSetLDT locSetLDT = getServices().getTypeConverter().getLocSetLDT();
            bindRuleSet(d, "cnf_setComm",
                add(SetsSmallerThanFeature.create(instOf("commRight"), instOf("commLeft"),
                    locSetLDT),
                    NotInScopeOfModalityFeature.INSTANCE, longConst(-800)));
        } else {
            bindRuleSet(d, "cnf_setComm", inftyConst());
        }

        bindRuleSet(d, "simplify_literals",
            // ifZero ( ConstraintStrengthenFeatureUC.create(proof),
            // longConst ( 0 ),
            longConst(-8000));

        bindRuleSet(d, "nonDuplicateAppCheckEq", EqNonDuplicateAppFeature.INSTANCE);

        // TODO: rename rule set?
        bindRuleSet(d, "comprehensions",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-50)));

        bindRuleSet(d, "comprehensions_high_costs",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(10000)));

        bindRuleSet(d, "comprehensions_low_costs",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-5000)));

        // features influenced by the strategy options
        /*
         * boolean useBlockExpand = strategyProperties.getProperty(
         * StrategyProperties.BLOCK_OPTIONS_KEY). equals(StrategyProperties.BLOCK_EXPAND);
         */

        final String queryAxProp =
            strategyProperties.getProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY);
        switch (queryAxProp) {
            case StrategyProperties.QUERYAXIOM_ON ->
                bindRuleSet(d, "query_axiom", longConst(-3000));
            case StrategyProperties.QUERYAXIOM_OFF -> bindRuleSet(d, "query_axiom", inftyConst());
            default -> throw new RuntimeException("Unexpected strategy property " + queryAxProp);
        }

        if (classAxiomApplicationEnabled()) {
            bindRuleSet(d, "classAxiom", longConst(-250));
        } else {
            bindRuleSet(d, "classAxiom", inftyConst());
        }

        /*
         * bindRuleSet ( d, "block_expand", useBlockExpand ? longConst ( 0 ) : inftyConst () );
         */

        // partial inv axiom
        bindRuleSet(d, "partialInvAxiom",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(10000)));

        // inReachableState
        bindRuleSet(d, "inReachableStateImplication",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(100)));

        // limit observer (must have better priority than "classAxiom")
        bindRuleSet(d, "limitObserver",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-200)));

        setupUserTaclets(d);

        setupSystemInvariantSimp(d);

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

        bindRuleSet(d, "inReachableStateImplication", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "limitObserver", NonDuplicateAppModPositionFeature.INSTANCE);
        bindRuleSet(d, "partialInvAxiom", NonDuplicateAppModPositionFeature.INSTANCE);

        setupClassAxiomApproval(d);

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
    public <GOAL extends ProofGoal<@NonNull GOAL>> RuleAppCost computeCost(@NonNull RuleApp app,
            @NonNull PosInOccurrence pio,
            @NonNull GOAL goal,
            @NonNull MutableState mState) {
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

    @Override
    protected RuleSetDispatchFeature getCostDispatcher() {
        return costComputationDispatcher;
    }
}
