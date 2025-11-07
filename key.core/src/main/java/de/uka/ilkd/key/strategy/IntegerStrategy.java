/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.util.HashSet;
import java.util.Set;

import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termgenerator.MultiplesModEquationsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.RootsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.FocusInAntecFeature;
import org.key_project.prover.strategy.costbased.feature.ScaleFeature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.SequentFormulasGenerator;
import org.key_project.prover.strategy.costbased.termgenerator.SubtermGenerator;

import org.jspecify.annotations.NonNull;

/// This strategy implements reasoning for integer arithmetics. In particular,
/// it supports linear integer arithmetics via Gaussian elimination,
/// Fourier-Motzkin; and non-linear integer reasoning via cross-multiplication
/// and Gröbner basis.
///
/// Do not create directly, instead use [IntegerStrategyFactory].
public class IntegerStrategy extends AbstractFeatureStrategy implements ComponentStrategy {

    public static final Name NAME = new Name("Integer Strategy");

    /// Magic constants
    private static final int IN_EQ_SIMP_NON_LIN_COST = 1000;
    private static final int POLY_DIVISION_COST = -2250;

    /// The features defining the three phases: cost computation, approval,
    /// additionalInstanceCreationAndEvaluation
    private final RuleSetDispatchFeature costComputationDispatcher;
    private final RuleSetDispatchFeature approvalDispatcher;
    private final RuleSetDispatchFeature instantiationDispatcher;

    /// Useful [TermFeature] collections
    private final ArithTermFeatures tf;
    private final FormulaTermFeatures ff;

    /// configuration options extracted from [StrategyProperties]
    private final boolean nonLinearArithmeticEnabled;
    private final boolean divAndModuloReasoningEnabled;
    private final boolean stopAtFirstNonCloseableGoal;

    public IntegerStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof);
        this.tf = new ArithTermFeatures(proof.getServices().getTypeConverter().getIntegerLDT());
        this.ff = new FormulaTermFeatures(this.tf);

        // determine configuration
        nonLinearArithmeticEnabled = StrategyProperties.NON_LIN_ARITH_COMPLETION.equals(
            strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY));

        divAndModuloReasoningEnabled =
            nonLinearArithmeticEnabled || StrategyProperties.NON_LIN_ARITH_DEF_OPS.equals(
                strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY));

        stopAtFirstNonCloseableGoal =
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE);

        // setup cost computations
        costComputationDispatcher = setupCostComputationF();
        approvalDispatcher = setupApprovalDispatcher();
        instantiationDispatcher = setupInstantiationF();

    }

    @Override
    public boolean isResponsibleFor(RuleSet rs) {
        return costComputationDispatcher.get(rs) != null || instantiationDispatcher.get(rs) != null;
    }

    @Override
    public Set<RuleSet> getResponsibilities() {
        var set = new HashSet<RuleSet>();
        set.addAll(costComputationDispatcher.ruleSets());
        set.addAll(instantiationDispatcher.ruleSets());
        return set;
    }

    private RuleSetDispatchFeature setupInstantiationF() {
        enableInstantiate();

        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        setupArithPrimaryCategories(d);
        setupDefOpsPrimaryCategories(d);
        setupInstantiationWithoutRetry(d);
        setupInEqSimpInstantiation(d);

        disableInstantiate();
        return d;
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

        return d;
    }

    private RuleSetDispatchFeature setupCostComputationF() {
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();
        final IntegerLDT numbers = getServices().getTypeConverter().getIntegerLDT();

        bindRuleSet(d, "simplify_int", inftyConst());

        setupArithPrimaryCategories(d);
        setupPolySimp(d, numbers);
        setupInEqSimp(d, numbers);

        setupDefOpsPrimaryCategories(d);

        bindRuleSet(d, "order_terms",
            add(applyTF("commEqRight", tf.monomial), applyTF("commEqLeft", tf.polynomial),
                monSmallerThan("commEqLeft", "commEqRight", numbers), longConst(-5000)));

        final TermBuffer equation = new TermBuffer();
        final TermBuffer left = new TermBuffer();
        final TermBuffer right = new TermBuffer();
        bindRuleSet(d, "apply_equations",
            SumFeature.createSum(
                add(applyTF(FocusProjection.create(0), tf.monomial),
                    ScaleFeature.createScaled(FindRightishFeature.create(numbers), 5.0)),
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
                                    add(applyTF(left, tf.nonNegOrNonCoeffMonomial),
                                        applyTF(right, tf.polynomial),
                                        MonomialsSmallerThanFeature.create(right, left,
                                            numbers)))))))),
                longConst(-4000)));

        final TermBuffer l = new TermBuffer();
        final TermBuffer r = new TermBuffer();
        bindRuleSet(d, "apply_equations_andOr",
            add(let(l, instOf("applyEqLeft"),
                let(r, instOf("applyEqRight"),
                    add(applyTF(l, tf.nonNegOrNonCoeffMonomial), applyTF(r, tf.polynomial),
                        MonomialsSmallerThanFeature.create(r, l, numbers)))),
                longConst(-150)));

        // For taclets that need instantiation, but where the instantiation is
        // deterministic and does not have to be repeated at a later point, we
        // setup the same feature terms as in the instantiation method. The
        // definitions in <code>setupInstantiationWithoutRetry</code> should
        // give cost infinity to those incomplete rule applications that will
        // never be instantiated (so that these applications can be removed from
        // the queue and do not have to be considered again).
        setupInstantiationWithoutRetry(d);

        return d;
    }

    private boolean arithNonLinInferences() {
        return nonLinearArithmeticEnabled;
    }

    private boolean arithDefOps() {
        return divAndModuloReasoningEnabled;
    }

    @Override
    public boolean isStopAtFirstNonCloseableGoal() {
        return stopAtFirstNonCloseableGoal;
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
                add(FocusInAntecFeature.getInstance(),
                    applyTF(FocusFormulaProjection.INSTANCE, atLeastTwoLCEquation))),
            ReducibleMonomialsFeature.createReducible(focus, eqLeft));

        final Feature eqMonomialFeature = add(not(directlyBelowSymbolAtIndex(tf.mul, -1)),
            ifZero(MatchedAssumesFeature.INSTANCE, let(focus, FocusProjection.create(0),
                let(eqLeft, sub(AssumptionProjection.create(0), 0), validEqApplication))));

        bindRuleSet(d, "polySimp_applyEq", add(eqMonomialFeature, longConst(1)));

        bindRuleSet(d, "polySimp_applyEqRigid", add(eqMonomialFeature, longConst(2)));

        //
        bindRuleSet(d, "defOps_expandModulo",
            add(NonDuplicateAppModPositionFeature.INSTANCE, longConst(-600)));

        // category "saturate"

        bindRuleSet(d, "polySimp_critPair",
            ifZero(MatchedAssumesFeature.INSTANCE,
                add(monSmallerThan("cpLeft1", "cpLeft2", numbers),
                    not(TrivialMonomialLCRFeature.create(instOf("cpLeft1"), instOf("cpLeft2"))))));
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
                        // no possible division has been found so far
                        add(NotInScopeOfModalityFeature.INSTANCE, ifZero(isReduciblePolyE,
                            // try again later
                            longConst(-POLY_DIVISION_COST)))))),
                longConst(100)));

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
                ifZero(MatchedAssumesFeature.INSTANCE,
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
        final Feature biggerLeftSide =
            MonomialsSmallerThanFeature.create(instOf("newSymLeft"),
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
                ifZero(MatchedAssumesFeature.INSTANCE,
                    SumFeature.createSum(applyTFNonStrict("esCoeff1", tf.nonNegLiteral),
                        applyTF("esRight1", tf.polynomial),
                        not(PolynomialValuesCmpFeature.leq(instOf("esRight2"), instOf("esRight1"),
                            instOfNonStrict("esCoeff1"), instOfNonStrict("esCoeff2")))))));

        // category "propagation"

        bindRuleSet(d, "inEqSimp_contradInEqs",
            add(applyTF("contradLeft", tf.monomial),
                ifZero(MatchedAssumesFeature.INSTANCE,
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
                ifZero(MatchedAssumesFeature.INSTANCE,
                    SumFeature.createSum(applyTF("contradRightSmaller", tf.polynomial),
                        applyTF("contradRightBigger", tf.polynomial), PolynomialValuesCmpFeature
                                .lt(instOf("contradRightSmaller"), instOf("contradRightBigger")))),
                longConst(-60)));

        bindRuleSet(d, "inEqSimp_strengthen", longConst(-30));

        bindRuleSet(d, "inEqSimp_subsumption",
            add(applyTF("subsumLeft", tf.monomial),
                ifZero(MatchedAssumesFeature.INSTANCE,
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

        final Term tOne = getServices().getTermBuilder().zTerm("1");
        final TermBuffer one = new TermBuffer() {
            @Override
            public void setContent(Term term, MutableState mState) {}

            @Override
            public @NonNull Term getContent(MutableState mState) {
                return tOne;
            }

            @Override
            public @NonNull Term toTerm(RuleApp app, PosInOccurrence pos,
                    Goal goal, MutableState mState) {
                return tOne;
            }
        };

        final JTerm tTwo = getServices().getTermBuilder().zTerm("2");
        final TermBuffer two = new TermBuffer() {
            @Override
            public void setContent(Term term, MutableState mState) {}

            @Override
            public @NonNull Term getContent(MutableState mState) {
                return tTwo;
            }

            @Override
            public @NonNull Term toTerm(RuleApp app, PosInOccurrence pos,
                    Goal goal, MutableState mState) {
                return tTwo;
            }
        };

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
        bindRuleSet(d, "inEqSimp_nonLin_multiply", add(
            applyTF("multLeft", tf.nonNegMonomial),
            applyTF("multRight", tf.polynomial),
            ifZero(MatchedAssumesFeature.INSTANCE,
                SumFeature.createSum(
                    applyTF("multFacLeft", tf.nonNegMonomial),
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
            ifZero(MatchedAssumesFeature.INSTANCE,
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
                        ifZero(MatchedAssumesFeature.INSTANCE,
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

        // noinspection unchecked
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

        final Feature exSubsumedModulus = add(applyTF("divDenom", tf.literal),
            not(sum(superTerm,
                SuperTermGenerator.upwardsWithIndex(sub(or(tf.addF, tf.mulF), any()),
                    getServices()),
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
    public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
        return !(approvalDispatcher.computeCost(app, pio, goal,
            new MutableState()) == TopRuleAppCost.INSTANCE);

    }

    @Override
    public RuleAppCost instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
            MutableState mState) {
        return instantiationDispatcher.computeCost(app, pio, goal, mState);
    }

    @Override
    public Name name() {
        return NAME;
    }

    @Override
    public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
            PosInOccurrence pos, Goal goal, MutableState mState) {
        return this.costComputationDispatcher.computeCost(app, pos, goal, mState);
    }

    @Override
    public RuleSetDispatchFeature getCostDispatcher() {
        return costComputationDispatcher;
    }
}
