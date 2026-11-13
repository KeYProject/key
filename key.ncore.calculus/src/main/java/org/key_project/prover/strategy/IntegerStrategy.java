/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import java.util.HashSet;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.*;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.IBuiltInRule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.*;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Monomial;
import org.key_project.prover.strategy.costbased.termProjection.AssumptionProjection;
import org.key_project.prover.strategy.costbased.termProjection.FocusFormulaProjection;
import org.key_project.prover.strategy.costbased.termProjection.FocusProjection;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.RelevantSequentFormulasGenerator;
import org.key_project.prover.strategy.costbased.termgenerator.SequentFormulasGenerator;
import org.key_project.prover.strategy.costbased.termgenerator.SubtermGenerator;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;
import org.key_project.util.QuadFunction;

import org.jspecify.annotations.Nullable;

/// This strategy implements reasoning for integer arithmetics. In particular,
/// it supports linear integer arithmetics via Gaussian elimination,
/// Fourier-Motzkin; and non-linear integer reasoning via cross-multiplication
/// and Gröbner basis.
///
/// This abstract strategy is independent of the concrete KeY instance but
/// assumes and requires a certain signature of integer symbols (as defined by
/// [IIntLdt]) and rule sets.
public abstract class IntegerStrategy<G extends ProofGoal<G>> extends AbstractFeatureStrategy<G>
        implements ComponentStrategy<G> {
    /// Reads better than a bare boolean at the call sites of [#setupMultiplyInequations].
    private static final boolean AT_APPROVAL = true;
    private static final boolean AT_COST = false;

    public static final Name NAME = new Name("Integer Strategy");

    /// Magic constants
    private static final int IN_EQ_SIMP_NON_LIN_COST = 1000;

    private static final int POLY_DIVISION_COST = -2250;

    /// The features defining the three phases: cost computation, approval,
    /// additionalInstanceCreationAndEvaluation
    private final RuleSetDispatchFeature costComputationDispatcher = new RuleSetDispatchFeature();
    private final RuleSetDispatchFeature approvalDispatcher = new RuleSetDispatchFeature();
    private final RuleSetDispatchFeature instantiationDispatcher = new RuleSetDispatchFeature();

    /// Useful [TermFeature] collections
    protected final ArithTermFeatures tf;
    protected final IFormulaTermFeatures ff;

    /// enum for the different arithmetic treatments
    protected enum ArithTreatment {
        /// Non-linear arithmetic switched off.
        BASIC,
        /// Inequations are cross-multiplied but only in a bound and capped manner.
        /// Division and modulo are expanded by their defining axioms.
        DEF_OPS,
        /// Cross-multiplication is admitted more freely, and equation splitting, case
        /// distinctions and cuts are added on top.
        MODEL_SEARCH
    }

    /// configuration options extracted from {@code StrategyProperties}
    protected final ArithTreatment arith;
    private final boolean stopAtFirstNonCloseableGoal;

    private final IIntLdt numbers;

    final FeatureConstants<G> fc;

    private final BiFunction<Term, LogicServices, Monomial> monomialBuilder;

    protected Config cfg;

    public IntegerStrategy(Config cfg, IFormulaTermFeatures ff,
            FeatureConstants<G> featureConstants) {
        this.tf = cfg.tf();
        this.ff = ff;
        this.cfg = cfg;
        // determine configuration
        if (cfg.nonLinearArithmeticEnabled()) {
            arith = ArithTreatment.MODEL_SEARCH;
        } else if (cfg.divAndModuloReasoningEnabled()) {
            arith = ArithTreatment.DEF_OPS;
        } else {
            arith = ArithTreatment.BASIC;
        }
        this.stopAtFirstNonCloseableGoal = cfg.stopAtFirstNonCloseableGoal();

        this.fc = featureConstants;

        this.numbers = cfg.numbers();
        this.monomialBuilder = cfg.monomialBuilder();
    }

    protected void init() {
        // setup cost computations
        setupCostComputationF(costComputationDispatcher);
        setupApprovalDispatcher(approvalDispatcher);
        setupInstantiationF(instantiationDispatcher);
    }

    private void setupInstantiationF(RuleSetDispatchFeature d) {
        enableInstantiate();

        setupArithPrimaryCategories(d);
        setupDefOpsPrimaryCategories(d);
        setupInstantiationWithoutRetry(d);
        setupInEqSimpInstantiation(d);

        // The multiply_2_inEq* taclets used to receive their instantiation cost from the
        // inEqSimp_nonLin rule set (bound in setupArithPrimaryCategories above). Now that
        // they only carry inEqSimp_nonLin_multiply, bind that rule set here explicitly.
        // Both Model Search and DefOps must complete cross-multiplication candidates (the
        // \assumes clause is matched during instantiation), so both get the finite stock
        // cost; Basic keeps them uninstantiated at infinity. Model Search stays
        // byte-identical because this reproduces the value inEqSimp_nonLin gave it.
        bindRuleSet(d, "inEqSimp_nonLin_multiply",
            arith != ArithTreatment.BASIC ? longConst(IN_EQ_SIMP_NON_LIN_COST)
                    : inftyConst());

        disableInstantiate();
    }


    protected void setupApprovalDispatcher(RuleSetDispatchFeature d) {
        if (arith != ArithTreatment.BASIC) {
            // The InEquationMultFeature bounding enforced here is what prevents
            // cross-multiplication from running in circles: only products that are
            // bounded by the left side of an inequation already present in the
            // sequent are approved, so the derivable monomials are capped. In
            // DefOps mode the check is stricter (exact match only) to avoid the
            // saturation blow-up acceptable for Model Search.
            // baseCost is zero on the approval dispatcher: approval only distinguishes
            // finite (approved) from infinite (rejected), so the base cost is irrelevant
            // here and left out to keep the approval decision identical to stock.
            setupMultiplyInequations(d, longConst(0), inftyConst(), AT_APPROVAL);
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

        bindRuleSet(d, "defOps_div", fc.nonDuplicateAppModPositionFeature());

        if (arith == ArithTreatment.MODEL_SEARCH) {
            setupInEqCaseDistinctionsApproval(d);
        }
    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null || instantiationDispatcher.get(rs) != null;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return stopAtFirstNonCloseableGoal;
    }

    private void setupCostComputationF(RuleSetDispatchFeature d) {
        bindRuleSet(d, "simplify_int", inftyConst());

        setupArithPrimaryCategories(d);
        setupPolySimp(d, numbers);
        setupInEqSimp(d, numbers);

        setupDefOpsPrimaryCategories(d);

        bindRuleSet(d, "order_terms",
            add(applyTF("commEqRight", tf.monomial), applyTF("commEqLeft", tf.polynomial),
                MonomialsSmallerThanFeature.<G>create(instOf("commEqLeft"), instOf("commEqRight"),
                    createTermOrdering(), numbers),
                CostBand.NORMALIZE.cost()));

        final TermBuffer equation = new TermBuffer();
        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();
        bindRuleSet(d, "apply_equations",
            SumFeature.createSum(
                add(applyTF(FocusProjection.<G>create(), tf.monomial),
                    ScaleFeature.createScaled(FindRightishFeature.create(numbers, tf.eq),
                        5.0)),
                ifZero(MatchedAssumesFeature.create(),
                    add(fc.checkApplyEqFeature(),
                        let(equation, AssumptionProjection.create(0),
                            add(not(applyTF(equation, ff.update())),
                                // there might be updates in
                                // front of the assumption
                                // formula; in this case we wait
                                // until the updates have
                                // been applied
                                let(left, sub(equation, 0),
                                    let(right, sub(equation, 1),
                                        add(applyTF(left, tf.nonNegOrNonCoeffMonomial),
                                            applyTF(right, tf.polynomial),
                                            MonomialsSmallerThanFeature.create(right, left,
                                                createTermOrdering(), numbers)))))))),
                longConst(CombinationCost.ORDERED_REWRITING)));

        final TermBuffer l = new TermBuffer();
        final TermBuffer r = new TermBuffer();
        bindRuleSet(d, "apply_equations_andOr",
            add(let(l, instOf("applyEqLeft"),
                let(r, instOf("applyEqRight"),
                    add(applyTF(l, tf.nonNegOrNonCoeffMonomial), applyTF(r, tf.polynomial),
                        MonomialsSmallerThanFeature.create(r, l, createTermOrdering(), numbers)))),
                longConst(CombinationCost.CNF_CONVERSION)));

        // For taclets that need instantiation, but where the instantiation is
        // deterministic and does not have to be repeated at a later point, we
        // setup the same feature terms as in the instantiation method. The
        // definitions in <code>setupInstantiationWithoutRetry</code> should
        // give cost infinity to those incomplete rule applications that will
        // never be instantiated (so that these applications can be removed from
        // the queue and do not have to be considered again).
        setupInstantiationWithoutRetry(d);
    }

    @Override
    public <Goal extends ProofGoal<Goal>> RuleAppCost computeCost(RuleApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        return this.costComputationDispatcher.computeCost(app, pos, goal, mState);
    }

    @Override
    public boolean isResponsibleFor(IBuiltInRule<G> rule) {
        return false;
    }

    @Override
    public Set<RuleSet> getResponsibilities(StrategyAspect aspect) {
        return new HashSet<>(getDispatcher(aspect).ruleSets());
    }

    @Override
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, G goal) {
        return !(approvalDispatcher.computeCost(app, pio, goal,
            new MutableState()) == TopRuleAppCost.INSTANCE);

    }

    @Override
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, G goal,
            MutableState mState) {
        return instantiationDispatcher.computeCost(app, pio, goal, mState);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public RuleSetDispatchFeature getDispatcher(StrategyAspect aspect) {
        return switch (aspect) {
            case StrategyAspect.Cost -> costComputationDispatcher;
            case StrategyAspect.Instantiation -> instantiationDispatcher;
            case StrategyAspect.Approval -> approvalDispatcher;
        };
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
                not(sum(intRel, SequentFormulasGenerator.<G>antecedent(),
                    ifZero(isRootInferenceProducer(intRel),
                        sum(rootInf, cfg.roots().apply(intRel, getServices()),
                            not(eq(instOf("cutFormula"), rootInf)))))),
                ifZero(applyTF("cutFormula", opSub(tf.eq, tf.atom, tf.literal)),
                    let(atom, sub(StaticFeatureCollection.instOf("cutFormula"), 0), let(literal,
                        sub(StaticFeatureCollection.instOf("cutFormula"), 1),
                        allowInEqStrengthening(atom, literal)))))));
    }

    private Feature allowInEqStrengthening(TermBuffer atom, TermBuffer literal) {
        final TermBuffer antecFor = new TermBuffer();

        return add(not(succIntEquationExists()),
            not(sum(antecFor, SequentFormulasGenerator.<G>antecedent(),
                not(applyTF(antecFor, add(or(tf.leqF, tf.geqF),
                    sub(fc.createEqTermFeature(atom),
                        fc.createEqTermFeature(literal))))))));
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

        bindRuleSet(d, "polySimp_expand", CostBand.SIMPLIFY.cost());
        bindRuleSet(d, "polySimp_directEquations", CostBand.SOLVE.cost());
        bindRuleSet(d, "polySimp_pullOutGcd", PolynomialCost.PULLOUT_GCD);
        bindRuleSet(d, "polySimp_leftNonUnit", CostBand.ENLARGE.cost());
        bindRuleSet(d, "polySimp_saturate", CostBand.DEFAULT.cost());

        // Omega test for handling linear arithmetic and inequalities over the
        // integers; cross-multiplication + case distinctions for nonlinear
        // inequalities

        bindRuleSet(d, "inEqSimp_expand", CostBand.SIMPLIFY.at(100));
        bindRuleSet(d, "inEqSimp_directInEquations", CostBand.SOLVE.at(100));
        bindRuleSet(d, "inEqSimp_propagation", LinearInequationCost.PROPAGATION);
        bindRuleSet(d, "inEqSimp_pullOutGcd", LinearInequationCost.PULLOUT_GCD_CONFLUENT);
        bindRuleSet(d, "inEqSimp_saturate", LinearInequationCost.SATURATE);
        bindRuleSet(d, "inEqSimp_forNormalisation", LinearInequationCost.FOR_NORMALISATION);
        bindRuleSet(d, "inEqSimp_special_nonLin", NonlinearArithmeticCost.DIVIDE_INEQUATION);

        if (arith == ArithTreatment.MODEL_SEARCH) {
            bindRuleSet(d, "inEqSimp_nonLin", NonlinearArithmeticCost.MULTIPLY);
        } else {
            bindRuleSet(d, "inEqSimp_nonLin", inftyConst());
        }
        bindRuleSet(d, "polyDivision", DivModCost.POLY_DIVISION);
    }

    private void setupPolySimp(RuleSetDispatchFeature d, IIntLdt numbers) {
        // category "expansion" (normalising polynomial terms)

        bindRuleSet(d, "polySimp_elimSubNeg", longConst(PolynomialCost.EXPAND));

        bindRuleSet(d, "polySimp_homo",
            add(applyTF("homoRight", add(not(tf.zeroLiteral), tf.polynomial)),
                or(applyTF("homoLeft", or(tf.addF, tf.negMonomial)),
                    not(MonomialsSmallerThanFeature.<G>create(instOf("homoRight"),
                        instOf("homoLeft"), createTermOrdering(), numbers))),
                longConst(PolynomialCost.EXPAND)));

        bindRuleSet(d, "polySimp_pullOutFactor", add(applyTFNonStrict("pullOutLeft", tf.literal),
            applyTFNonStrict("pullOutRight", tf.literal), longConst(PolynomialCost.EXPAND)));

        bindRuleSet(d, "polySimp_elimOneLeft", PolynomialCost.EXPAND);

        bindRuleSet(d, "polySimp_elimOneRight", PolynomialCost.EXPAND);

        bindRuleSet(d, "polySimp_mulOrder", add(applyTF("commRight", tf.monomial), or(
            applyTF("commLeft", tf.addF),
            add(applyTF("commLeft", tf.atom),
                AtomsSmallerThanFeature.<G>create(instOf("commLeft"), instOf("commRight"),
                    createTermOrdering(), numbers))),
            longConst(PolynomialCost.MUL_ORDER)));

        bindRuleSet(d, "polySimp_mulAssoc",
            SumFeature.createSum(applyTF("mulAssocMono0", tf.monomial),
                applyTF("mulAssocMono1", tf.monomial), applyTF("mulAssocAtom", tf.atom),
                longConst(PolynomialCost.MUL_ASSOC)));

        bindRuleSet(d, "polySimp_addOrder",
            SumFeature.createSum(applyTF("commLeft", tf.monomial),
                applyTF("commRight", tf.polynomial),
                MonomialsSmallerThanFeature.<G>create(instOf("commRight"), instOf("commLeft"),
                    createTermOrdering(), numbers),
                longConst(PolynomialCost.ADD_ORDER)));

        bindRuleSet(d, "polySimp_addAssoc",
            SumFeature.createSum(applyTF("addAssocPoly0", tf.polynomial),
                applyTF("addAssocPoly1", tf.polynomial), applyTF("addAssocMono", tf.monomial),
                longConst(PolynomialCost.ADD_ASSOC)));

        bindRuleSet(d, "polySimp_dist",
            SumFeature.createSum(applyTF("distSummand0", tf.polynomial),
                applyTF("distSummand1", tf.polynomial),
                ifZero(applyTF("distCoeff", tf.monomial), longConst(PolynomialCost.DISTRIBUTE + 20),
                    applyTF("distCoeff", tf.polynomial)),
                longConst(PolynomialCost.DISTRIBUTE)));

        // category "direct equations"

        bindRuleSet(d, "polySimp_balance",
            SumFeature
                    .createSum(applyTF("sepResidue", tf.polynomial),
                        ifZero(isInstantiated("sepPosMono"),
                            add(applyTF("sepPosMono", tf.nonNegMonomial),
                                MonomialsSmallerThanFeature.<G>create(instOf("sepResidue"),
                                    instOf("sepPosMono"), createTermOrdering(), numbers))),
                        ifZero(isInstantiated("sepNegMono"),
                            add(applyTF("sepNegMono", tf.negMonomial),
                                MonomialsSmallerThanFeature.<G>create(instOf("sepResidue"),
                                    instOf("sepNegMono"), createTermOrdering(), numbers))),
                        longConst(LinearEquationCost.BALANCE)));

        bindRuleSet(d, "polySimp_normalise", add(applyTF("invertRight", tf.zeroLiteral),
            applyTF("invertLeft", tf.negMonomial), longConst(LinearEquationCost.BALANCE)));

        // application of equations: some specialised rules that handle
        // monomials and their coefficients properly

        final TermBuffer eqLeft = new TermBuffer();
        final TermBuffer focus = new TermBuffer();

        final TermFeature atLeastTwoLCEquation =
            opSub(tf.eq, opSub(tf.mul, tf.atom, tf.atLeastTwoLiteral), tf.intF);

        final Feature validEqApplication =
            add(not(eq(eqLeft, focus, fc::createEqTermFeature)),
                // otherwise, the normal equation rules can and should
                // be used
                ifZero(
                    StaticFeatureCollection.applyTF(AssumptionProjection.create(0),
                        atLeastTwoLCEquation),
                    add(FocusInAntecFeature.getInstance(),
                        applyTF(FocusFormulaProjection.<G>create(), atLeastTwoLCEquation))),
                ReducibleMonomialsFeature.createReducible(focus, eqLeft, monomialBuilder));

        final Feature eqMonomialFeature = add(
            not(fc.directlyBelowSymbolAtIndex(tf.mul, -1)),
            ifZero(MatchedAssumesFeature.create(),
                let(focus, FocusProjection.create(),
                    let(eqLeft, sub(AssumptionProjection.<G>create(0), 0), validEqApplication))));

        bindRuleSet(d, "polySimp_applyEq",
            add(eqMonomialFeature, longConst(LinearEquationCost.APPLY_EQ_MONOMIAL_TIEBREAK)));

        bindRuleSet(d, "polySimp_applyEqRigid",
            add(eqMonomialFeature, longConst(LinearEquationCost.APPLY_EQ_MONOMIAL_TIEBREAK + 1)));

        //
        bindRuleSet(d, "defOps_expandModulo",
            add(fc.nonDuplicateAppModPositionFeature(),
                longConst(DivModCost.EXPAND_MODULO)));

        // category "saturate"

        bindRuleSet(d, "polySimp_critPair",
            ifZero(MatchedAssumesFeature.create(),
                add(MonomialsSmallerThanFeature.<G>create(instOf("cpLeft1"), instOf("cpLeft2"),
                    createTermOrdering(), numbers),
                    not(TrivialMonomialLCRFeature.<G>create(instOf("cpLeft1"),
                        instOf("cpLeft2"), monomialBuilder)))));
    }

    private void setupDivModDivision(RuleSetDispatchFeature d) {
        final TermBuffer denomLC = new TermBuffer();
        final TermBuffer numTerm = new TermBuffer();
        final TermBuffer divCoeff = new TermBuffer();

        // exact polynomial division

        final Feature checkNumTerm = ifZero(
            add(not(applyTF(numTerm, tf.addF)),
                ReducibleMonomialsFeature.createReducible(numTerm, denomLC, monomialBuilder)),
            add(instantiate("polyDivCoeff",
                cfg.reduceMonomials.apply(numTerm, denomLC)),
                inftyConst()));

        final Feature isReduciblePoly =
            sum(numTerm,
                SubtermGenerator.<G>rightTraverse(StaticFeatureCollection.instOf("divNum"),
                    tf.addF),
                checkNumTerm);

        // polynomial division modulo equations of the antecedent

        final Feature checkCoeffE = ifZero(
            contains(divCoeff, FocusProjection.create(), fc::createEqTermFeature),
            // do not apply if the result contains the original term
            longConst(0), add(instantiate("polyDivCoeff", divCoeff), inftyConst()));

        final Feature isReduciblePolyE =
            sum(numTerm,
                SubtermGenerator.<G>rightTraverse(StaticFeatureCollection.instOf("divNum"),
                    tf.addF),
                ifZero(applyTF(numTerm, tf.addF), longConst(0), sum(divCoeff,
                    cfg.multiplesModEquations().apply(numTerm, denomLC),
                    checkCoeffE)));

        bindRuleSet(d, "defOps_divModPullOut",
            SumFeature.createSum(
                not(add(applyTF("divNum", tf.literal), applyTF("divDenom", tf.literal))),
                applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                ifZero(applyTF("divDenom", tf.addF),
                    let(denomLC, sub(StaticFeatureCollection.instOf("divDenom"), 1),
                        not(isReduciblePoly)),
                    let(denomLC, instOf("divDenom"), ifZero(isReduciblePoly,
                        // no possible division has been found so far
                        add(fc.notInScopeOfModalityFeature(), ifZero(isReduciblePolyE,
                            // try again later
                            longConst(-DivModCost.POLY_DIVISION)))))),
                CostBand.DEFAULT.at(100)));

    }


    // For taclets that need instantiation, but where the instantiation is
    // deterministic and does not have to be repeated at a later point, we
    // setup the same feature terms as in the instantiation method. The
    // definitions in <code>setupInstantiationWithoutRetry</code> should
    // give cost infinity to those incomplete rule applications that will
    // never be instantiated (so that these applications can be removed from
    // the queue and do not have to be considered again).
    private void setupPolySimpInstantiationWithoutRetry(RuleSetDispatchFeature d) {
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
                    cfg.monomialColumnOp.apply(instOf("newSymLeftCoeff"),
                        instOf("newSymRight"))))));

        final TermBuffer divisor = new TermBuffer();
        final TermBuffer dividend = new TermBuffer();

        bindRuleSet(d, "polySimp_applyEqPseudo",
            add(applyTF("aePseudoTargetLeft", tf.monomial),
                applyTF("aePseudoTargetRight", tf.polynomial),
                ifZero(MatchedAssumesFeature.create(),
                    SumFeature.createSum(DiffFindAndAssumesFeature.create(),
                        applyTF("aePseudoLeft", add(tf.nonCoeffMonomial, not(tf.atom))),
                        applyTF("aePseudoLeftCoeff", tf.atLeastTwoLiteral),
                        applyTF("aePseudoRight", tf.polynomial),
                        MonomialsSmallerThanFeature.<G>create(instOf("aePseudoRight"),
                            instOf("aePseudoLeft"), createTermOrdering(), numbers),
                        let(divisor, StaticFeatureCollection.instOf("aePseudoLeft"),
                            let(dividend, StaticFeatureCollection.instOf("aePseudoTargetLeft"),
                                add(ReducibleMonomialsFeature.createReducible(dividend,
                                    divisor, monomialBuilder),
                                    instantiate("aePseudoTargetFactor",
                                        cfg.reduceMonomials.apply(dividend,
                                            divisor)))))))));
    }

    private void setupNewSymApproval(RuleSetDispatchFeature d, IIntLdt numbers) {
        final TermBuffer antecFor = new TermBuffer();
        final Feature columnOpEq = applyTF(antecFor,
            opSub(tf.eq, opSub(tf.mul, tf.atom, tf.atLeastTwoLiteral), tf.polynomial));
        final Feature biggerLeftSide =
            MonomialsSmallerThanFeature.create(instOf("newSymLeft"),
                subAt(antecFor, PosInTerm.getTopLevel().down(0).down(0)), createTermOrdering(),
                numbers);
        bindRuleSet(d, "polySimp_newSym", add(isInstantiated("newSymDef"), sum(antecFor,
            SequentFormulasGenerator.<G>antecedent(), not(add(columnOpEq, biggerLeftSide)))));
    }

    private void setupPullOutGcd(RuleSetDispatchFeature d, String ruleSet, boolean roundingUp) {
        final TermBuffer gcd = new TermBuffer();

        final Feature instantiateDivs;
        if (roundingUp) {
            instantiateDivs = add(
                instantiate("elimGcdLeftDiv",
                    cfg.roundingUpDividePolynomials().apply(gcd,
                        instOf("elimGcdLeft"))),
                instantiate("elimGcdRightDiv",
                    cfg.roundingUpDividePolynomials().apply(gcd,
                        instOf("elimGcdRight"))));
        } else {
            instantiateDivs = add(
                instantiate("elimGcdLeftDiv",
                    cfg.roundingDownDividePolynomials().apply(gcd,
                        instOf("elimGcdLeft"))),
                instantiate("elimGcdRightDiv",
                    cfg.roundingDownDividePolynomials().apply(gcd,
                        instOf("elimGcdRight"))));
        }
        bindRuleSet(d, ruleSet,
            add(applyTF("elimGcdLeft", tf.nonNegMonomial), applyTF("elimGcdRight", tf.polynomial),
                let(gcd,
                    cfg.coeffGcd().apply(instOf("elimGcdLeft"),
                        instOf("elimGcdRight")),
                    add(applyTF(gcd, tf.atLeastTwoLiteral), instantiate("elimGcd", gcd),
                        instantiateDivs))));
    }

    private void setupInEqSimp(RuleSetDispatchFeature d, IIntLdt numbers) {
        // category "expansion" (normalising inequations)

        bindRuleSet(d, "inEqSimp_moveLeft", LinearInequationCost.MOVE_LEFT);

        bindRuleSet(d, "inEqSimp_makeNonStrict", LinearInequationCost.MAKE_NON_STRICT);

        bindRuleSet(d, "inEqSimp_commute",
            SumFeature.createSum(applyTF("commRight", tf.monomial),
                applyTF("commLeft", tf.polynomial),
                MonomialsSmallerThanFeature.<G>create(instOf("commLeft"), instOf("commRight"),
                    createTermOrdering(), numbers),
                longConst(LinearInequationCost.COMMUTE)));

        // this is copied from "polySimp_homo"
        bindRuleSet(d, "inEqSimp_homo",
            add(applyTF("homoRight", add(not(tf.zeroLiteral), tf.polynomial)),
                or(applyTF("homoLeft", or(tf.addF, tf.negMonomial)),
                    not(MonomialsSmallerThanFeature.<G>create(instOf("homoRight"),
                        instOf("homoLeft"), createTermOrdering(), numbers)))));

        // category "direct inequations"

        // this is copied from "polySimp_balance"
        bindRuleSet(d, "inEqSimp_balance",
            add(applyTF("sepResidue", tf.polynomial),
                ifZero(isInstantiated("sepPosMono"),
                    add(applyTF("sepPosMono", tf.nonNegMonomial),
                        MonomialsSmallerThanFeature.<G>create(instOf("sepResidue"),
                            instOf("sepPosMono"), createTermOrdering(), numbers))),
                ifZero(isInstantiated("sepNegMono"), add(applyTF("sepNegMono", tf.negMonomial),
                    MonomialsSmallerThanFeature.<G>create(instOf("sepResidue"),
                        instOf("sepNegMono"), createTermOrdering(), numbers)))));

        // this is copied from "polySimp_normalise"
        bindRuleSet(d, "inEqSimp_normalise",
            add(applyTF("invertRight", tf.zeroLiteral), applyTF("invertLeft", tf.negMonomial)));

        // category "saturate"

        bindRuleSet(d, "inEqSimp_antiSymm", longConst(LinearInequationCost.ANTISYMM));

        bindRuleSet(d, "inEqSimp_exactShadow",
            SumFeature.createSum(applyTF("esLeft", tf.nonCoeffMonomial),
                applyTFNonStrict("esCoeff2", tf.nonNegLiteral), applyTF("esRight2", tf.polynomial),
                ifZero(MatchedAssumesFeature.create(),
                    SumFeature.createSum(applyTFNonStrict("esCoeff1", tf.nonNegLiteral),
                        applyTF("esRight1", tf.polynomial),
                        not(cfg.polyLeqCoeff.apply(instOf("esRight2"),
                            instOf("esRight1"),
                            instOfNonStrict("esCoeff1"), instOfNonStrict("esCoeff2")))))));

        // category "propagation"

        bindRuleSet(d, "inEqSimp_contradInEqs",
            add(applyTF("contradLeft", tf.monomial),
                ifZero(MatchedAssumesFeature.create(),
                    SumFeature.createSum(DiffFindAndAssumesFeature.create(),
                        applyTF("contradRightSmaller", tf.polynomial),
                        applyTF("contradRightBigger", tf.polynomial),
                        applyTFNonStrict("contradCoeffSmaller", tf.posLiteral),
                        applyTFNonStrict("contradCoeffBigger", tf.posLiteral),
                        cfg.polyLtCoeff().apply(
                            instOf("contradRightSmaller"),
                            instOf("contradRightBigger"), instOfNonStrict("contradCoeffBigger"),
                            instOfNonStrict("contradCoeffSmaller"))))));

        bindRuleSet(d, "inEqSimp_contradEqs",
            add(applyTF("contradLeft", tf.monomial),
                ifZero(MatchedAssumesFeature.create(),
                    SumFeature.createSum(applyTF("contradRightSmaller", tf.polynomial),
                        applyTF("contradRightBigger", tf.polynomial),
                        cfg.polyLt.apply(
                            instOf("contradRightSmaller"),
                            instOf("contradRightBigger")))),
                longConst(LinearInequationCost.CONTRAD)));

        bindRuleSet(d, "inEqSimp_strengthen", longConst(LinearInequationCost.STRENGTHEN));

        bindRuleSet(d, "inEqSimp_subsumption",
            add(applyTF("subsumLeft", tf.monomial),
                ifZero(MatchedAssumesFeature.create(),
                    SumFeature.createSum(DiffFindAndAssumesFeature.create(),
                        applyTF("subsumRightSmaller", tf.polynomial),
                        applyTF("subsumRightBigger", tf.polynomial),
                        applyTFNonStrict("subsumCoeffSmaller", tf.posLiteral),
                        applyTFNonStrict("subsumCoeffBigger", tf.posLiteral),
                        cfg.polyLeqCoeff.apply(
                            instOf("subsumRightSmaller"),
                            instOf("subsumRightBigger"), instOfNonStrict("subsumCoeffBigger"),
                            instOfNonStrict("subsumCoeffSmaller"))))));

        // category "handling of non-linear inequations"

        if (arith == ArithTreatment.MODEL_SEARCH) {
            setupMultiplyInequations(d, longConst(IN_EQ_SIMP_NON_LIN_COST),
                CostBand.DEFAULT.at(100),
                AT_COST);

            bindRuleSet(d, "inEqSimp_split_eq",
                add(fc.topLevelFindSucc(),
                    longConst(NonlinearArithmeticCost.SPLIT_EQ)));

            bindRuleSet(d, "inEqSimp_signCases", not(isInstantiated("signCasesLeft")));
        } else if (arith == ArithTreatment.DEF_OPS) {
            // DefOps also cross-multiplies inequations, but - unlike Model Search - does
            // no equation splitting, case distinctions or cuts, and only multiplies when
            // the product exactly matches the left side of an inequation already in the
            // sequent, which the approval dispatcher enforces. DefOps proofs without
            // integer inequations enqueue no multiply candidates and keep their stock
            // search path.
            setupMultiplyInequations(d, longConst(IN_EQ_SIMP_NON_LIN_COST), longConst(100),
                AT_COST);
        } else {
            // Basic arithmetic: cross-multiplication is off. inEqSimp_nonLin used to be
            // the off-switch via the (now removed) tag on the multiply taclets, so the
            // multiply rule set must be pinned to infinity explicitly.
            bindRuleSet(d, "inEqSimp_nonLin_multiply", inftyConst());
        }

        // category "normalisation of formulas"
        // (e.g., quantified formulas, where the normal sequent calculus
        // does not do any normalisation)

        bindRuleSet(d, "inEqSimp_and_contradInEqs",
            SumFeature.createSum(applyTF("contradLeft", tf.monomial),
                applyTF("contradRightSmaller", tf.polynomial),
                applyTF("contradRightBigger", tf.polynomial),
                cfg.polyLt.apply(
                    instOf("contradRightSmaller"), instOf("contradRightBigger"))));

        bindRuleSet(d, "inEqSimp_andOr_subsumption",
            SumFeature.createSum(applyTF("subsumLeft", tf.monomial),
                applyTF("subsumRightSmaller", tf.polynomial),
                applyTF("subsumRightBigger", tf.polynomial),
                cfg.polyLeq.apply(
                    instOf("subsumRightSmaller"), instOf("subsumRightBigger"))));

        bindRuleSet(d, "inEqSimp_and_subsumptionEq",
            SumFeature.createSum(applyTF("subsumLeft", tf.monomial),
                applyTF("subsumRightSmaller", tf.polynomial),
                applyTF("subsumRightBigger", tf.polynomial),
                cfg.polyLt().apply(
                    instOf("subsumRightSmaller"), instOf("subsumRightBigger"))));

        final Term tOne = zTerm("1");
        final TermBuffer one = new TermBuffer() {
            @Override
            public void setContent(@Nullable Term term, MutableState mState) {}

            @Override
            public Term getContent(MutableState mState) {
                return tOne;
            }

            @Override
            public Term toTerm(RuleApp app, PosInOccurrence pos,
                    ProofGoal<?> goal, MutableState mState) {
                return tOne;
            }
        };

        final Term tTwo = zTerm("2");
        final TermBuffer two = new TermBuffer() {
            @Override
            public void setContent(@Nullable Term term, MutableState mState) {}

            @Override
            public Term getContent(MutableState mState) {
                return tTwo;
            }

            @Override
            public Term toTerm(RuleApp app, PosInOccurrence pos,
                    ProofGoal<?> goal, MutableState mState) {
                return tTwo;
            }
        };

        bindRuleSet(d, "inEqSimp_or_tautInEqs",
            SumFeature.createSum(applyTF("tautLeft", tf.monomial),
                applyTF("tautRightSmaller", tf.polynomial),
                applyTF("tautRightBigger", tf.polynomial),
                cfg.polyLeq().apply(instOf("tautRightSmaller"),
                    fc.opTerm(numbers.getAdd(), one, instOf("tautRightBigger")))));

        bindRuleSet(d, "inEqSimp_or_weaken",
            SumFeature.createSum(applyTF("weakenLeft", tf.monomial),
                applyTF("weakenRightSmaller", tf.polynomial),
                applyTF("weakenRightBigger", tf.polynomial),
                cfg.polyEq.apply(
                    fc.opTerm(numbers.getAdd(), one, instOf("weakenRightSmaller")),
                    instOf("weakenRightBigger"))));

        bindRuleSet(d, "inEqSimp_or_antiSymm",
            SumFeature.createSum(applyTF("antiSymmLeft", tf.monomial),
                applyTF("antiSymmRightSmaller", tf.polynomial),
                applyTF("antiSymmRightBigger", tf.polynomial),
                cfg.polyEq().apply(
                    fc.opTerm(numbers.getAdd(), two, instOf("antiSymmRightSmaller")),
                    instOf("antiSymmRightBigger"))));

    }

    /// Sets up the cost/approval features for the cross-multiplication of inequations
    /// (rule set inEqSimp\_nonLin\_multiply).
    ///
    /// The multiply\_2\_inEq\* taclets used to carry the inEqSimp\_nonLin rule set in addition to
    /// inEqSimp\_nonLin\_multiply, which contributed the base cost [#IN_EQ_SIMP_NON_LIN_COST]
    /// and, in DefOps mode, the infinite off-switch. They no longer do; the base cost is therefore
    /// passed in explicitly via `baseCost` so that inEqSimp\_nonLin can keep its stock cost
    /// and DefOps proofs that never cross-multiply stay on their stock path.
    ///
    /// @param d the dispatcher to bind the features to
    /// @param baseCost cost added unconditionally (previously supplied by the inEqSimp\_nonLin
    /// rule set); zero for the approval dispatcher, [#IN_EQ_SIMP_NON_LIN_COST] for
    /// the cost dispatcher
    /// @param notAllowedF the costs in case the multiplication is not allowed
    /// @param atApproval whether the features are bound to the approval dispatcher, which is the
    /// only place a limit can be enforced that depends on how far the proof has come: a
    /// candidate's cost is computed when it enters the queue, while the sequent and the
    /// branch keep growing until it is applied
    private void setupMultiplyInequations(RuleSetDispatchFeature d, Feature baseCost,
            Feature notAllowedF, boolean atApproval) {
        // In DefOps a product is admitted only when it exactly matches the left side of an
        // inequation already in the sequent, so multiplication stays directed at monomials the
        // proof is asking about. Model Search also admits products merely subsumed by such a
        // left side, and saturates more speculatively.
        final boolean onlyExactlyBounded = arith == ArithTreatment.DEF_OPS;
        // The branch limit exists to stop DefOps saturating; Model Search is expected to
        // saturate and keeps its unlimited behaviour.
        final boolean capBranch = atApproval && arith == ArithTreatment.DEF_OPS;
        final TermBuffer intRel = new TermBuffer();

        /*
         * final Feature partiallyBounded = not ( sum ( intRel, SequentFormulasGenerator.sequent (),
         * not ( add ( applyTF ( intRel, tf.intRelation ), InEquationMultFeature .partiallyBounded (
         * instOf ( "multLeft" ), instOf ( "multFacLeft" ), sub ( intRel, 0 ) ) ) ) ) );
         */

        final Feature intRelation = applyTF(intRel, tf.intRelation);
        final var relevantSequentFormulas =
            RelevantSequentFormulasGenerator.<G>sequent(tf.intRelationOp);

        final Feature totallyBounded = not(sum(intRel, relevantSequentFormulas,
            not(add(
                InEquationMultFeature.<G>totallyBounded(instOf("multLeft"),
                    instOf("multFacLeft"),
                    sub(intRel, 0), monomialBuilder),
                intRelation))));
        final Feature exactlyBounded = new IsBoundedByInequationFeature<G>(
            instOf("multLeft"), instOf("multFacLeft"), tf.intRelation, monomialBuilder);

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
        bindRuleSet(d, "inEqSimp_nonLin_multiply", add(
            baseCost,
            applyTF("multLeft", tf.nonNegMonomial),
            applyTF("multRight", tf.polynomial),
            ifZero(MatchedAssumesFeature.create(),
                SumFeature.createSum(
                    applyTF("multFacLeft", tf.nonNegMonomial),
                    ifZero(applyTF("multRight", tf.literal), CostBand.DEFAULT.at(-100)),
                    ifZero(applyTF("multFacRight", tf.literal),
                        CostBand.DEFAULT.at(-100),
                        applyTF("multFacRight", tf.polynomial)),
                    /*
                     * ifZero ( applyTF ( "multRight", tf.literal ), longConst ( -100 ), applyTF (
                     * "multRight", tf.polynomial ) ), ifZero ( applyTF ( "multFacRight", tf.literal
                     * ), longConst ( -100 ), applyTF ( "multFacRight", tf.polynomial ) ),
                     */
                    not(TermSmallerThanFeature.<G>create(FocusProjection.create(),
                        AssumptionProjection.create(0), createTermOrdering())),
                    onlyExactlyBounded
                            ? ifZero(add(applyTF("multLeft", tf.linearMonomial),
                                applyTF("multFacLeft", tf.linearMonomial)), longConst(0),
                                notAllowedF)
                            : longConst(0),

                    capBranch
                            ? ifZero(getBranchCountFeatureFor("multiply_2_inEq"), longConst(0),
                                notAllowedF)
                            : longConst(0),
                    ifZero(exactlyBounded, CostBand.DEFAULT.cost(),
                        onlyExactlyBounded ? notAllowedF
                                : ifZero(totallyBounded, CostBand.DEFAULT.at(100), notAllowedF))
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

    protected abstract Feature getBranchCountFeatureFor(String prefix);

    private void setupInEqSimpInstantiation(RuleSetDispatchFeature d) {
        // category "handling of non-linear inequations"

        setupSquaresAreNonNegative(d);

        if (arith == ArithTreatment.MODEL_SEARCH) {
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
        bindRuleSet(d, "inEqSimp_pullOutGcd_antec",
            LinearInequationCost.PULLOUT_GCD_ANTEC_NONCONFLUENT);

        // category "handling of non-linear inequations"

        final TermBuffer divisor = new TermBuffer();
        final TermBuffer dividend = new TermBuffer();

        bindRuleSet(d, "inEqSimp_nonLin_divide", SumFeature.createSum(
            applyTF("divProd", tf.nonCoeffMonomial),
            applyTFNonStrict("divProdBoundNonPos", tf.nonPosLiteral),
            applyTFNonStrict("divProdBoundNonNeg", tf.nonNegLiteral),
            ifZero(MatchedAssumesFeature.create(),
                let(divisor, instOf("divX"), let(dividend, instOf("divProd"),
                    SumFeature.createSum(applyTF(divisor, tf.nonCoeffMonomial),
                        not(eq(dividend, divisor)), applyTFNonStrict("divXBoundPos", tf.posLiteral),
                        applyTFNonStrict("divXBoundNeg", tf.negLiteral),
                        ReducibleMonomialsFeature.createReducible(dividend, divisor,
                            monomialBuilder),
                        instantiate(
                            "divY", cfg.reduceMonomials().apply(dividend,
                                divisor))))))));

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
                        ifZero(MatchedAssumesFeature.create(),
                            let(divisor, instOf("divX"), let(dividend, instOf("divProd"),
                                SumFeature.createSum(applyTF(divisor, tf.nonCoeffMonomial),
                                    not(applyTF(dividend,
                                        fc.createEqTermFeature(divisor))),
                                    applyTFNonStrict("divXBoundNonPos", tf.nonPosLiteral),
                                    applyTFNonStrict("divXBoundNonNeg", tf.nonNegLiteral),
                                    ReducibleMonomialsFeature.createReducible(dividend,
                                        divisor, monomialBuilder),
                                    let(quotient,
                                        cfg.reduceMonomials().apply(dividend,
                                            divisor),
                                        add(
                                            sum(antecFor, SequentFormulasGenerator.<G>antecedent(),
                                                not(applyTF(antecFor,
                                                    pos ? opSub(tf.geq,
                                                        fc
                                                                .createEqTermFeature(quotient),
                                                        tf.posLiteral)
                                                            : opSub(tf.leq,
                                                                fc
                                                                        .createEqTermFeature(
                                                                            quotient),
                                                                tf.negLiteral)))),
                                            instantiate("divY", quotient)))))))));
    }

    private void setupSquaresAreNonNegative(RuleSetDispatchFeature d) {
        final TermBuffer intRel = new TermBuffer();
        final TermBuffer product = new TermBuffer();
        final TermBuffer factor = new TermBuffer();

        final Feature productContainsSquare =
            applyTF(sub(product, 0),
                or(fc.createEqTermFeature(factor),
                    opSub(tf.mul, any(), fc.createEqTermFeature(factor))));
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
                        longConst(NonlinearArithmeticCost.MULTIPLY + 200)
                    // ,
                    // applyTF ( atom, rec ( any (),
                    // longTermConst ( 5 ) ) )
                    ))));

        bindRuleSet(d, "inEqSimp_signCases", posNegSplitting);

        final Feature strengthening = forEach(intRel, SequentFormulasGenerator.antecedent(),
            SumFeature.createSum(
                applyTF(intRel, add(or(tf.geqF, tf.leqF), sub(tf.atom, tf.literal))),
                instantiate("cutFormula",
                    fc.opTerm(tf.eq, sub(intRel, 0), sub(intRel, 1))),
                longConst(NonlinearArithmeticCost.MULTIPLY + 300)
            // ,
            // applyTF ( sub ( intRel, 0 ),
            // rec ( any (), longTermConst ( 5 ) ) )
            ));

        final Feature rootInferences = forEach(intRel, SequentFormulasGenerator.antecedent(),
            add(isRootInferenceProducer(intRel),
                forEach(rootInf, (TermGenerator<G>) cfg.roots.apply(intRel, getServices()),
                    add(instantiate("cutFormula", rootInf),
                        ifZero(applyTF(rootInf, ff.orF()),
                            CostBand.DEFAULT.at(50)),
                        ifZero(applyTF(rootInf, ff.andF()),
                            CostBand.DEFAULT.at(20)))),
                longConst(NonlinearArithmeticCost.MULTIPLY)));

        bindRuleSet(d, "cut", oneOf(new Feature[] { strengthening, rootInferences }));
    }

    private Feature isRootInferenceProducer(TermBuffer intRel) {
        return applyTF(intRel, add(tf.intRelation, sub(tf.nonCoeffMonomial, tf.literal)));
    }

    private Feature allowPosNegCaseDistinction(TermBuffer atom) {
        final TermBuffer antecFor = new TermBuffer();
        final TermFeature eqAtom = fc.createEqTermFeature(atom);

        return add(not(succIntEquationExists()),
            sum(antecFor, SequentFormulasGenerator.<G>antecedent(),
                not(applyTF(antecFor, or(opSub(tf.eq, eqAtom, any()),
                    opSub(tf.leq, eqAtom, tf.negLiteral), opSub(tf.geq, eqAtom, tf.posLiteral))))));
    }

    private Feature succIntEquationExists() {
        final TermBuffer succFor = new TermBuffer();

        return not(sum(succFor, RelevantSequentFormulasGenerator.<G>succedent(tf.intEquation),
            not(applyTF(succFor, tf.intEquation))));
    }

    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////
    //
    // Axiomatisation and algorithms for further arithmetic operations:
    // division, modulus, modular Java operations
    //
    // //////////////////////////////////////////////////////////////////////////
    // //////////////////////////////////////////////////////////////////////////

    protected void setupDefOpsPrimaryCategories(RuleSetDispatchFeature d) {
        if (arith != ArithTreatment.BASIC) {
            // the axiom defining division only has to be inserted once, because
            // it adds equations to the antecedent
            bindRuleSet(d, "defOps_div",
                SumFeature.createSum(fc.nonDuplicateAppModPositionFeature(),
                    applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                    applyTF("divNum", tf.notContainsDivMod),
                    applyTF("divDenom", tf.notContainsDivMod),
                    ifZero(isBelow(ff.modalOperator()), longConst(DivModCost.BELOW_MODALITY))));

            setupDefOpsExpandMod(d);

            bindRuleSet(d, "defOps_expandRanges", DivModCost.EXPAND_RANGES);
            bindRuleSet(d, "defOps_expandJNumericOp", DivModCost.EXPAND_NUMERIC_OP);
            bindRuleSet(d, "defOps_modHomoEq", DivModCost.MOD_HOMO_EQ);
        } else {
            bindRuleSet(d, "defOps_div", inftyConst());

            bindRuleSet(d, "defOps_mod", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.literal), longConst(DivModCost.MOD)));

            bindRuleSet(d, "defOps_expandRanges", inftyConst());
            bindRuleSet(d, "defOps_expandJNumericOp", inftyConst());
            bindRuleSet(d, "defOps_modHomoEq", inftyConst());
        }
    }

    private void setupDefOpsExpandMod(RuleSetDispatchFeature d) {
        final TermBuffer superTerm = new TermBuffer();

        final Feature subsumedModulus =
            add(applyTF(superTerm, sub(opSub(tf.mod, any(), tf.literal), tf.zeroLiteral)),
                cfg.polyDivides().apply(instOf("divDenom"),
                    sub(sub(superTerm, 0), 1)));

        final Feature exSubsumedModulus = add(applyTF("divDenom", tf.literal),
            not(sum(superTerm,
                fc.upwardsWithIndexSuperGenerator(sub(or(tf.addF, tf.mulF), any()),
                    getServices()),
                not(subsumedModulus))));

        bindRuleSet(d, "defOps_mod",
            ifZero(add(applyTF("divNum", tf.literal), applyTF("divDenom", tf.literal)),
                longConst(DivModCost.MOD),
                SumFeature.createSum(applyTF("divNum", tf.polynomial),
                    applyTF("divDenom", tf.polynomial),
                    ifZero(isBelow(ff.modalOperator()), exSubsumedModulus,
                        or(add(applyTF("divNum", tf.notContainsDivMod),
                            applyTF("divDenom", tf.notContainsDivMod)), exSubsumedModulus)),
                    longConst(DivModCost.MOD_EXPAND))));
    }

    /// For taclets that need instantiation, but where the instantiation is deterministic and does
    /// not have to be repeated at a later point, we set up the same feature terms both in the cost
    /// computation method and in the instantiation method. The definitions in
    /// `setupInstantiationWithoutRetry` should give cost infinity to those incomplete
    /// rule applications that will never be instantiated (so that these applications can be removed
    /// from the queue and do not have to be considered again).
    private void setupInstantiationWithoutRetry(RuleSetDispatchFeature d) {
        setupPolySimpInstantiationWithoutRetry(d);
        setupInEqSimpInstantiationWithoutRetry(d);
    }

    protected Feature eq(ProjectionToTerm t1, ProjectionToTerm t2) {
        final TermBuffer buf = new TermBuffer();
        return let(buf, t1, applyTF(t2, fc.createEqTermFeature(buf)));
    }

    protected abstract Term zTerm(String num);

    protected abstract LogicServices getServices();

    protected abstract TermOrdering createTermOrdering();

    public record Config(ArithTermFeatures tf, boolean nonLinearArithmeticEnabled,
            boolean divAndModuloReasoningEnabled,
            boolean stopAtFirstNonCloseableGoal, IIntLdt numbers,
            BiFunction<Term, LogicServices, Monomial> monomialBuilder,
            BinaryOperator<ProjectionToTerm> reduceMonomials,
            BinaryOperator<ProjectionToTerm> monomialColumnOp,
            BinaryOperator<ProjectionToTerm> roundingUpDividePolynomials,
            BinaryOperator<ProjectionToTerm> roundingDownDividePolynomials,
            BinaryOperator<ProjectionToTerm> coeffGcd,
            BiFunction<ProjectionToTerm, ProjectionToTerm, Feature> polyLt,
            QuadFunction<ProjectionToTerm, ProjectionToTerm, ProjectionToTerm, ProjectionToTerm, Feature> polyLtCoeff,
            BiFunction<ProjectionToTerm, ProjectionToTerm, Feature> polyLeq,
            QuadFunction<ProjectionToTerm, ProjectionToTerm, ProjectionToTerm, ProjectionToTerm, Feature> polyLeqCoeff,
            BiFunction<ProjectionToTerm, ProjectionToTerm, Feature> polyEq,
            BiFunction<ProjectionToTerm, ProjectionToTerm, Feature> polyDivides,
            BiFunction<ProjectionToTerm, ProjectionToTerm, TermGenerator<?>> multiplesModEquations,
            BiFunction<ProjectionToTerm, LogicServices, TermGenerator<?>> roots) {
    }
}
