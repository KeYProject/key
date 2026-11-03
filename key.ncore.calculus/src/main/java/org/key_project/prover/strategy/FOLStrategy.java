/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import java.util.HashSet;
import java.util.Set;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.LogicServices;
import org.key_project.logic.Name;
import org.key_project.logic.TermOrdering;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.*;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.feature.instantiator.ChoicePoint;
import org.key_project.prover.strategy.costbased.termProjection.*;
import org.key_project.prover.strategy.costbased.termfeature.IsNonRigidTermFeature;

import static org.key_project.prover.strategy.costbased.FOLCost.*;

/// Strategy for general FOL rules. This does not consider other
/// theories like integers or Java-specific functions.
///
/// In particular, instantiation of quantifiers is not supported by this
/// strategy, as the current E-matching depends on the theory of integers.
public abstract class FOLStrategy<G extends ProofGoal<G>> extends AbstractFeatureStrategy<G>
        implements ComponentStrategy<G> {
    public static final Name NAME = new Name("FOL Strategy");

    private final RuleSetDispatchFeature costComputationDispatcher;
    private final RuleSetDispatchFeature approvalDispatcher;
    private final RuleSetDispatchFeature instantiationDispatcher;
    private final Feature costComputationF;
    private final Feature approvalF;
    private final Feature instantiationF;

    protected final ArithTermFeatures tf;
    protected final IFormulaTermFeatures ff;

    private final TermOrdering termOrdering;
    private final IIntLdt numbers;

    final FeatureConstants<G> fc;

    public FOLStrategy(ArithTermFeatures tf, IFormulaTermFeatures ff,
            FeatureConstants<G> featureConstants, TermOrdering termOrdering, IIntLdt numbers) {
        this.tf = tf;
        this.ff = ff;

        this.fc = featureConstants;

        this.termOrdering = termOrdering;
        this.numbers = numbers;

        costComputationDispatcher = setupCostComputationF();
        approvalDispatcher = setupApprovalDispatcher();
        instantiationDispatcher = setupInstantiationF();

        costComputationF = setUpGlobalF(costComputationDispatcher);
        instantiationF = setUpGlobalF(instantiationDispatcher);
        approvalF = approvalDispatcher;
    }

    protected Feature setUpGlobalF(RuleSetDispatchFeature d) {
        return d;
    }

    private RuleSetDispatchFeature setupCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "closure", CostBand.CLOSE.cost());
        bindRuleSet(d, "alpha", CostBand.DECOMPOSE.cost());
        bindRuleSet(d, "delta", CostBand.TYPE.cost());
        bindRuleSet(d, "simplify_boolean", CostBand.PREFER.at(300));

        final Feature findDepthFeature =
            FindDepthFeature.getInstance();

        bindRuleSet(d, "concrete",
            add(CostBand.REWRITE.cost(),
                ScaleFeature.createScaled(findDepthFeature, 10.0)));
        bindRuleSet(d, "simplify", CostBand.SIMPLIFY.cost());
        bindRuleSet(d, "simplify_enlarging", CostBand.ENLARGE.cost());
        bindRuleSet(d, "simplify_ENLARGING", CostBand.ENLARGE.at(100));

        // always give infinite cost to obsolete rules
        bindRuleSet(d, "obsolete", inftyConst());

        bindRuleSet(d, "no_self_application",
            ifZero(MatchedAssumesFeature.create(), NoSelfApplicationFeature.create()));

        bindRuleSet(d, "find_term_not_in_assumes", ifZero(MatchedAssumesFeature.create(),
            not(contains(AssumptionProjection.create(0), FocusProjection.create(),
                fc::createEqTermFeature))));

        bindRuleSet(d, "update_elim",
            add(CostBand.ELIMINATE.cost(),
                ScaleFeature.createScaled(findDepthFeature, 10.0)));
        bindRuleSet(d, "update_apply_on_update",
            add(CostBand.DECOMPOSE.cost(),
                ScaleFeature.createScaled(findDepthFeature, 10.0)));
        bindRuleSet(d, "update_join", CostBand.SIMPLIFY.at(-100));
        bindRuleSet(d, "update_apply", CostBand.SIMPLIFY.cost());

        setupSplitting(d);

        bindRuleSet(d, "gamma", add(not(isInstantiated("t")),
            ifZero(allowQuantifierSplitting(), CostBand.DEFAULT.cost(),
                CostBand.DEFAULT.at(50))));
        bindRuleSet(d, "gamma_destructive", inftyConst());

        bindRuleSet(d, "triggered",
            add(not(TriggerVarInstantiatedFeature.create()), CostBand.DEFER.cost()));

        bindRuleSet(d, "comprehension_split",
            add(applyTF(FocusFormulaProjection.<G>create(), ff.notContainsExecutable()),
                ifZero(allowQuantifierSplitting(), CostBand.DEFER.at(2000),
                    CostBand.DEFER.at(4500))));

        setupReplaceKnown(d);

        setupEquationReasoning(d);

        bindRuleSet(d, "order_terms",
            add(TermSmallerThanFeature.<G>create(instOf("commEqLeft"), instOf("commEqRight"),
                termOrdering),
                CostBand.NORMALIZE.cost()));

        bindRuleSet(d, "try_apply_subst",
            add(fc.eqNonDuplicateAppFeature(), CostBand.SUBST.cost()));

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
        bindRuleSet(d, "apply_equations", fc.eqNonDuplicateAppFeature());

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
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, G goal,
            MutableState mState) {
        return instantiationF.computeCost(app, pio, goal, mState);
    }

    @Override
    public Set<RuleSet> getResponsibilities(StrategyAspect aspect) {
        return new HashSet<>(getDispatcher(aspect).ruleSets());
    }

    @Override
    public RuleSetDispatchFeature getDispatcher(StrategyAspect aspect) {
        return switch (aspect) {
            case StrategyAspect.Cost -> costComputationDispatcher;
            case StrategyAspect.Instantiation -> instantiationDispatcher;
            case StrategyAspect.Approval -> approvalDispatcher;
        };
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null || instantiationDispatcher.get(rs) != null
                || approvalDispatcher.get(rs) != null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return false;
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, G goal) {
        return approvalF.computeCost(app, pio, goal, new MutableState()) != TopRuleAppCost.INSTANCE;
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
    public <GOAL extends ProofGoal<GOAL>> RuleAppCost computeCost(RuleApp app, PosInOccurrence pio,
            GOAL goal, MutableState mState) {
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
            CostBand.PREFER.cost(),
            ScaleFeature.createScaled(FindDepthFeature.getInstance(), 10.0)));

        bindRuleSet(d, "moveQuantToLeft",
            add(quantifiersMightSplit() ? CostBand.DEFAULT.cost()
                    : applyTF(FocusFormulaProjection.<G>create(), ff.quantifiedPureLitConjDisj()),
                CostBand.PREFER.at(-50)));

        bindRuleSet(d, "conjNormalForm",
            ifZero(
                add(or(FocusInAntecFeature.getInstance(), notBelowQuantifier()),
                    fc.notInScopeOfModalityFeature()),
                add(longConst(CombinationCost.CNF_CONVERSION),
                    ScaleFeature.createScaled(FindDepthFeature.getInstance(), 20)),
                inftyConst()));

        bindRuleSet(d, "elimQuantifier", CostBand.PREFER.at(-500));
        bindRuleSet(d, "elimQuantifierWithCast", CostBand.DEFAULT.at(50));

        final TermBuffer<G> left = new TermBuffer<>();
        final TermBuffer<G> right = new TermBuffer<>();
        bindRuleSet(d, "apply_equations_andOr",
            add(let(left, instOf("applyEqLeft"),
                let(right, instOf("applyEqRight"),
                    TermSmallerThanFeature.create(right, left,
                        termOrdering))),
                longConst(CombinationCost.CNF_CONVERSION)));

        final ProjectionToTerm<G> focus = FocusProjection.create();
        bindRuleSet(d, "distrQuantifier",
            add(or(
                applyTF(focus,
                    add(ff.quantifiedClauseSet(), not(opSub(ff.all(), ff.orF())),
                        fc.createEliminableQuantifier())),
                SumFeature.createSum(onlyInScopeOfQuantifiers(),
                    fc.splittableQuantifiedFormula(),
                    ifZero(FocusInAntecFeature.getInstance(),
                        applyTF(focus, sub(ff.andF())),
                        applyTF(focus, sub(ff.orF()))))),
                longConst(QUANTIFIER_DISTRIBUTION)));

        bindRuleSet(d, "swapQuantifiers",
            add(applyTF(focus, add(ff.quantifiedClauseSet(),
                fc.createEliminableQuantifier(), sub(not(fc.createEliminableQuantifier())))),
                longConst(QUANTIFIER_DISTRIBUTION)));

        // category "conjunctive normal form"

        bindRuleSet(d, "cnf_orAssoc",
            SumFeature.createSum(applyTF("assoc0", ff.clause()),
                applyTF("assoc1", ff.clause()), applyTF("assoc2", ff.literal()),
                longConst(CNF_RESTRUCTURE - 45)));

        bindRuleSet(d, "cnf_andAssoc",
            SumFeature.createSum(applyTF("assoc0", ff.clauseSet()),
                applyTF("assoc1", ff.clauseSet()), applyTF("assoc2", ff.clause()),
                longConst(CNF_RESTRUCTURE + 25)));

        bindRuleSet(d, "cnf_dist",
            SumFeature.createSum(applyTF("distRight0", ff.clauseSet()),
                applyTF("distRight1", ff.clauseSet()), ifZero(applyTF("distLeft", ff.clause()),
                    longConst(CNF_RESTRUCTURE + 20), applyTF("distLeft", ff.clauseSet())),
                longConst(CNF_RESTRUCTURE)));

        final TermBuffer<G> superFor = new TermBuffer<>();
        final Feature onlyBelowQuanAndOr =
            sum(superFor, fc.superTermGenerator(any(), getServices()),
                applyTF(superFor, or(ff.quantifiedFor(), ff.andF(), ff.orF())));

        final Feature belowUnskolemisableQuantifier =
            ifZero(FocusInAntecFeature.getInstance(),
                not(sum(superFor, fc.superTermGenerator(any(), getServices()),
                    not(applyTF(superFor, op(ff.all()))))),
                not(sum(superFor, fc.superTermGenerator(any(), getServices()),
                    not(applyTF(superFor, op(ff.exists()))))));

        bindRuleSet(d, "cnf_expandIfThenElse", add(
            isBelow(ff.quantifierF()),
            onlyBelowQuanAndOr, belowUnskolemisableQuantifier));

        final Feature pullOutQuantifierAllowed =
            add(isBelow(ff.quantifierF()), onlyBelowQuanAndOr, applyTF(
                focus, sub(ff.quantifiedClauseSet(), ff.quantifiedClauseSet())));

        bindRuleSet(d, "pullOutQuantifierUnifying", PULL_OUT_QUANTIFIER);

        bindRuleSet(d, "pullOutQuantifierAll", add(pullOutQuantifierAllowed,
            ifZero(FocusInAntecFeature.getInstance(), longConst(PULL_OUT_QUANTIFIER),
                longConst(PULL_OUT_QUANTIFIER_REVERSE))));

        bindRuleSet(d, "pullOutQuantifierEx", add(pullOutQuantifierAllowed,
            ifZero(FocusInAntecFeature.getInstance(),
                longConst(PULL_OUT_QUANTIFIER_REVERSE),
                longConst(PULL_OUT_QUANTIFIER))));
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
            final TermBuffer<G> varInst = new TermBuffer<>();
            final Feature branchPrediction = fc.instantiationCostScaler(
                InstantiationCost.create(varInst, triggerTreatment()),
                allowQuantifierSplitting());

            bindRuleSet(d, "gamma",
                SumFeature.createSum(FocusInAntecFeature.getInstance(),
                    applyTF(FocusProjection.<G>create(0),
                        add(ff.quantifiedClauseSet(),
                            instQuantifiersWithQueries() ? longTermConst(0)
                                    : ff.notContainsExecutable())),
                    forEach(varInst, HeuristicInstantiation.forOption(triggerTreatment()),
                        add(instantiate("t", varInst),
                            add(branchPrediction,
                                CostBand.DEFAULT.at(10),
                                // orders candidates of one predicted-cost band by their
                                // connection to the sequent instead of formula position
                                InstantiationTieBreakFeature.create(varInst,
                                    triggersOption()))))));
            final TermBuffer<G> splitInst = new TermBuffer<>();

            bindRuleSet(d, "triggered",
                SumFeature.createSum(forEach(splitInst, fc.createTriggeredInstantiations(true),
                    add(instantiateTriggeredVariable(splitInst), CostBand.DEFER.cost())),
                    CostBand.DEFER.at(1000)));

        } else {
            bindRuleSet(d, "gamma", inftyConst());
            bindRuleSet(d, "triggered", inftyConst());
        }
    }

    private void setupQuantifierInstantiationApproval(RuleSetDispatchFeature d) {
        if (quantifierInstantiatedEnabled()) {
            final TermBuffer<G> varInst = new TermBuffer<>();

            bindRuleSet(d, "gamma", add(isInstantiated("t"),
                not(sum(varInst, HeuristicInstantiation.forOption(triggerTreatment()),
                    not(StaticFeatureCollection.eq(instOf("t"), varInst)))),
                InstantiationCostScalerFeature.create(
                    InstantiationCost.create(instOf("t"), triggerTreatment()),
                    longConst(0))));

            final TermBuffer<G> splitInst = new TermBuffer<>();
            bindRuleSet(d, "triggered",
                add(isTriggerVariableInstantiated(),
                    not(sum(splitInst, fc.createTriggeredInstantiations(false),
                        not(StaticFeatureCollection.eq(instOfTriggerVariable(), splitInst))))));
        } else {
            bindRuleSet(d, "gamma", inftyConst());
            bindRuleSet(d, "triggered", inftyConst());
        }
    }


    protected final Feature onlyInScopeOfQuantifiers() {
        final TermBuffer<G> buf = new TermBuffer<>();
        return sum(buf, fc.superTermGenerator(any(), getServices()),
            applyTF(buf, ff.quantifiedFor()));
    }

    protected Feature notBelowQuantifier() {
        final TermBuffer<G> superFor = new TermBuffer<>();
        return or(fc.topLevelFindAntecOrSucc(),
            sum(superFor, fc.superTermGenerator(any(), getServices()),
                not(applyTF(superFor, ff.quantifierF()))));
    }

    private void setupReplaceKnown(RuleSetDispatchFeature d) {
        final Feature commonF =
            add(ifZero(MatchedAssumesFeature.create(), DiffFindAndAssumesFeature.create()),
                CostBand.NORMALIZE.cost(),
                add(fc.diffFindAndReplacewithFeature(),
                    ScaleFeature.createScaled(fc.countMaxDPath(), 10.0)));

        bindRuleSet(d, "replace_known_left", commonF);

        bindRuleSet(d, "replace_known_right",
            add(commonF,
                ifZero(fc.directlyBelowSymbolAtIndex(ff.imp(), 1),
                    longConst(REPLACE_KNOWN_UNDER_CONNECTIVE),
                    ifZero(fc.directlyBelowSymbolAtIndex(ff.equiv(), -1),
                        longConst(REPLACE_KNOWN_UNDER_CONNECTIVE)))));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Application of beta- and cut-rules to handle disjunctions
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected void setupSplitting(RuleSetDispatchFeature d) {
        final TermBuffer<G> subFor = new TermBuffer<>();
        final Feature noCutsAllowed =
            sum(subFor, fc.allowedCutPositionsGenerator(), not(applyTF(subFor, ff.cutAllowed())));
        bindRuleSet(d, "beta",
            SumFeature.createSum(noCutsAllowed,
                ifZero(fc.purePosDPath(), CostBand.PREFER.at(300)),
                ScaleFeature.createScaled(fc.countPosDPath(), -3.0),
                ScaleFeature.createScaled(fc.countMaxDPath(), 10.0),
                CostBand.DEFAULT.at(20)));
        TermBuffer<G> superF = new TermBuffer<>();
        final ProjectionToTerm<G> focus = FocusProjection.create();
        final ProjectionToTerm<G> splitCondition = sub(focus, 0);
        bindRuleSet(d, "split_cond", add(// do not split over formulas containing auxiliary
            // variables
            applyTF(focus, rec(any(), not(fc.selectSkolemConstant()))),
            // prefer splits when condition has quantifiers (less
            // likely to be simplified away)
            applyTF(splitCondition,
                rec(ff.quantifiedFor(), ifZero(ff.quantifiedFor(), longTermConst(-10)))),
            FindDepthFeature.getInstance(), // prefer top level splits
            ScaleFeature.createAffine(fc.countOccurrences(splitCondition), -10, 10),
            sum(superF, fc.superTermGenerator(any(), getServices()),
                applyTF(superF, not(ff.elemUpdate()))),
            ifZero(applyTF(focus, fc.containsExecutableCodeTF()),
                CostBand.DEFAULT.at(-100), CostBand.DEFAULT.at(25))));
        ProjectionToTerm<G> cutFormula = instOf("cutFormula");
        Feature countOccurrencesInSeq =
            ScaleFeature.createAffine(fc.countOccurrences(cutFormula), -10, 10);
        bindRuleSet(d, "cut_direct",
            SumFeature
                    .createSum(
                        not(fc.topLevelFindAntecOrSuccWithUpdate()),
                        fc.allowedCutPositions(),
                        ifZero(notBelowQuantifier(),
                            add(
                                applyTF(cutFormula, add(ff.cutAllowed(),
                                    // do not cut over formulas containing
                                    // auxiliary variables
                                    rec(any(), not(fc.selectSkolemConstant())))),
                                countOccurrencesInSeq, // standard costs
                                longConst(CUT_DIRECT_STANDARD)),
                            SumFeature // check for cuts below quantifiers
                                    .createSum(applyTF(cutFormula, ff.cutAllowedBelowQuantifier()),
                                        applyTF(FocusFormulaProjection.<G>create(),
                                            ff.quantifiedClauseSet()),
                                        ifZero(allowQuantifierSplitting(),
                                            CostBand.DEFAULT.cost(),
                                            longConst(CUT_DIRECT_STANDARD))))));
    }

    private void setupSplittingApproval(RuleSetDispatchFeature d) {
        bindRuleSet(d, "beta", allowSplitting(FocusFormulaProjection.create()));

        bindRuleSet(d, "split_cond", allowSplitting(FocusProjection.create()));

        final TermBuffer<G> subFor = new TermBuffer<>();
        final Feature compareCutAllowed = ifZero(applyTF(subFor, ff.cutAllowed()),
            leq(applyTF("cutFormula", ff.cutPriority()), applyTF(subFor, ff.cutPriority())));

        final Feature noBetterCut =
            sum(subFor, fc.allowedCutPositionsGenerator(), compareCutAllowed);

        bindRuleSet(d, "cut_direct", add(allowSplitting(FocusFormulaProjection.create()),
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
        final TermBuffer<G> equation = new TermBuffer<>();
        final TermBuffer<G> left = new TermBuffer<>();
        final TermBuffer<G> right = new TermBuffer<>();

        // applying equations less deep/less leftish in terms/formulas is
        // preferred
        // this is important for reducing polynomials (start with the biggest
        // summands)
        bindRuleSet(d, "apply_equations",
            SumFeature.createSum(
                ifZero(MatchedAssumesFeature.create(),
                    add(fc.checkApplyEqFeature(), let(equation, AssumptionProjection.create(0),
                        add(not(applyTF(equation, ff.update())),
                            // there might be updates in
                            // front of the assumption
                            // formula; in this case we wait
                            // until the updates have
                            // been applied
                            let(left, sub(equation, 0),
                                let(right, sub(equation, 1),
                                    TermSmallerThanFeature.create(right, left,
                                        termOrdering))))))),
                longConst(CombinationCost.ORDERED_REWRITING)));

        bindRuleSet(d, "insert_eq_nonrigid",
            applyTF(FocusProjection.<G>create(0), IsNonRigidTermFeature.INSTANCE));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Queries for the active taclet options
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected abstract boolean instQuantifiersWithQueries();

    protected abstract boolean quantifiersMightSplit();

    protected abstract Feature allowQuantifierSplitting();

    /** the value of the trigger option, fixed when this strategy was constructed */
    protected abstract String triggersOption();

    protected abstract boolean quantifierInstantiatedEnabled();

    protected abstract Feature allowSplitting(ProjectionToTerm<G> focus);

    protected abstract boolean normalSplitting();

    protected abstract LogicServices getServices();
}
