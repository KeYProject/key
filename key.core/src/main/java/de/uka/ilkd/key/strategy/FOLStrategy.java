/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.quantifierHeuristics.*;
import de.uka.ilkd.key.strategy.termProjection.AssumptionProjection;
import de.uka.ilkd.key.strategy.termProjection.FocusFormulaProjection;
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termgenerator.AllowedCutPositionsGenerator;
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

/// Strategy for general FOL rules. This does not consider other
/// theories like integers or Java-specific functions.
///
/// In particular, instantiation of quantifiers is not supported by this
/// strategy, as the current E-matching depends on the theory of integers.
/// For that reason, instantiation can be found [JFOLStrategy].
public class FOLStrategy extends AbstractFeatureStrategy implements ComponentStrategy {
    public static final Name NAME = new Name("FOL Strategy");

    protected final StrategyProperties strategyProperties;

    private final RuleSetDispatchFeature costComputationDispatcher;
    private final RuleSetDispatchFeature approvalDispatcher;
    private final RuleSetDispatchFeature instantiationDispatcher;
    private final Feature costComputationF;
    private final Feature approvalF;
    private final Feature instantiationF;

    protected final ArithTermFeatures tf;
    protected final FormulaTermFeatures ff;

    public FOLStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);

        this.strategyProperties = (StrategyProperties) strategyProperties.clone();

        this.tf = new ArithTermFeatures(getServices().getTypeConverter().getIntegerLDT());
        this.ff = new FormulaTermFeatures(this.tf);

        costComputationDispatcher = setupCostComputationF();
        approvalDispatcher = setupApprovalDispatcher();
        instantiationDispatcher = setupInstantiationF();

        costComputationF = setUpGlobalF(costComputationDispatcher);
        instantiationF = setUpGlobalF(instantiationDispatcher);
        approvalF = approvalDispatcher;
    }

    private Feature setUpGlobalF(RuleSetDispatchFeature d) {
        final Feature oneStepSimplificationF =
            oneStepSimplificationFeature(longConst(-11000));
        return add(d, oneStepSimplificationF);
    }

    private Feature oneStepSimplificationFeature(Feature cost) {
        SetRuleFilter filter = new SetRuleFilter();
        filter.addRuleToSet(MiscTools.findOneStepSimplifier(getProof()));
        return ConditionalFeature.createConditional(filter, cost);
    }

    private RuleSetDispatchFeature setupCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

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

        // always give infinite cost to obsolete rules
        bindRuleSet(d, "obsolete", inftyConst());

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

        bindRuleSet(d, "gamma", add(not(isInstantiated("t")),
            ifZero(allowQuantifierSplitting(), longConst(0), longConst(50))));
        bindRuleSet(d, "gamma_destructive", inftyConst());

        bindRuleSet(d, "triggered", add(not(isTriggerVariableInstantiated()), longConst(500)));

        bindRuleSet(d, "comprehension_split",
            add(applyTF(FocusFormulaProjection.INSTANCE, ff.notContainsExecutable),
                ifZero(allowQuantifierSplitting(), longConst(2500), longConst(5000))));

        setupReplaceKnown(d);

        setupEquationReasoning(d);

        bindRuleSet(d, "order_terms",
            add(termSmallerThan("commEqLeft", "commEqRight"), longConst(-5000)));

        bindRuleSet(d, "simplify_instanceof_static",
            add(EqNonDuplicateAppFeature.INSTANCE, longConst(-500)));

        bindRuleSet(d, "evaluate_instanceof", longConst(-500));

        bindRuleSet(d, "instanceof_to_exists", TopLevelFindFeature.ANTEC);

        bindRuleSet(d, "try_apply_subst",
            add(EqNonDuplicateAppFeature.INSTANCE, longConst(-10000)));

        // delete cast
        bindRuleSet(d, "cast_deletion",
            ifZero(implicitCastNecessary(instOf("castedTerm")), longConst(-5000), inftyConst()));

        bindRuleSet(d, "type_hierarchy_def", -6500);

        bindRuleSet(d, "cut", not(isInstantiated("cutFormula")));

        if (quantifierInstantiatedEnabled()) {
            setupFormulaNormalisation(d);
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

        return d;
    }

    private RuleSetDispatchFeature setupApprovalDispatcher() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        setupQuantifierInstantiationApproval(d);
        setupSplittingApproval(d);

        // Without EqNonDuplicateAppFeature.INSTANCE
        // rule 'applyEq' might be applied on the same term
        // without changing the sequent for a really long time. This is tested by
        // TestSymbolicExecutionTreeBuilder#testInstanceOfNotInEndlessLoop()
        bindRuleSet(d, "apply_equations", EqNonDuplicateAppFeature.INSTANCE);

        return d;
    }

    private RuleSetDispatchFeature setupInstantiationF() {
        enableInstantiate();

        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        setupQuantifierInstantiation(d);

        disableInstantiate();
        return d;
    }

    @Override
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return instantiationF.computeCost(app, pio, goal, mState);
    }

    @Override
    public RuleSetDispatchFeature getCostDispatcher() {
        return costComputationDispatcher;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return approvalF.computeCost(app, pio, goal, new MutableState()) != TopRuleAppCost.INSTANCE;
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null || instantiationDispatcher.get(rs) != null
                || approvalDispatcher.get(rs) != null;
    }

    @Override
    public Set<RuleSet> getResponsibilities() {
        var set = new HashSet<RuleSet>();
        set.addAll(costComputationDispatcher.ruleSets());
        set.addAll(instantiationDispatcher.ruleSets());
        set.addAll(approvalDispatcher.ruleSets());
        return set;
    }

    @Override
    public Name name() {
        return NAME;
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
        return costComputationF.computeCost(app, pio, goal, mState);
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Normalisation of formulas; this is mostly a pre-processing step for
    // handling quantified formulas
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected void setupFormulaNormalisation(RuleSetDispatchFeature d) {
        bindRuleSet(d, "negationNormalForm", add(BelowBinderFeature.getInstance(),
            longConst(-500),
            ScaleFeature.createScaled(FindDepthFeature.getInstance(), 10.0)));

        bindRuleSet(d, "moveQuantToLeft",
            add(quantifiersMightSplit() ? longConst(0)
                    : applyTF(FocusFormulaProjection.INSTANCE, ff.quantifiedPureLitConjDisj),
                longConst(-550)));

        bindRuleSet(d, "conjNormalForm",
            ifZero(
                add(or(FocusInAntecFeature.getInstance(), notBelowQuantifier()),
                    NotInScopeOfModalityFeature.INSTANCE),
                add(longConst(-150),
                    ScaleFeature.createScaled(FindDepthFeature.getInstance(), 20)),
                inftyConst()));

        bindRuleSet(d, "setEqualityBlastingRight", longConst(-100));



        bindRuleSet(d, "elimQuantifier", -1000);
        bindRuleSet(d, "elimQuantifierWithCast", 50);

        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();
        bindRuleSet(d, "apply_equations_andOr",
            add(let(left, instOf("applyEqLeft"),
                let(right, instOf("applyEqRight"),
                    TermSmallerThanFeature.create(right, left))),
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

        bindRuleSet(d, "cnf_orAssoc",
            SumFeature.createSum(applyTF("assoc0", ff.clause),
                applyTF("assoc1", ff.clause), applyTF("assoc2", ff.literal), longConst(-80)));

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

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Application of beta- and cut-rules to handle disjunctions
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected void setupSplitting(RuleSetDispatchFeature d) {
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

    private void setupEquationReasoning(RuleSetDispatchFeature d) {
        final TermBuffer equation = new TermBuffer();
        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();

        // applying equations less deep/less leftish in terms/formulas is
        // preferred
        // this is important for reducing polynomials (start with the biggest
        // summands)
        bindRuleSet(d, "apply_equations",
            SumFeature.createSum(
                ifZero(MatchedAssumesFeature.INSTANCE,
                    add(CheckApplyEqFeature.INSTANCE, let(equation, AssumptionProjection.create(0),
                        add(not(applyTF(equation, ff.update)),
                            // there might be updates in
                            // front of the assumption
                            // formula; in this case we wait
                            // until the updates have
                            // been applied
                            let(left, sub(equation, 0),
                                let(right, sub(equation, 1),
                                    TermSmallerThanFeature.create(right, left))))))),
                longConst(-4000)));

        bindRuleSet(d, "insert_eq_nonrigid",
            applyTF(FocusProjection.create(0), IsNonRigidTermFeature.INSTANCE));
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

    @Override
    public boolean isResponsibleFor(BuiltInRule rule) {
        return rule instanceof OneStepSimplifier;
    }
}
