/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;


import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.EqTermFeature;
import de.uka.ilkd.key.strategy.termgenerator.MultiplesModEquationsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.RootsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.Term;
import org.key_project.logic.op.Operator;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.ArithTermFeatures;
import org.key_project.prover.strategy.ComponentStrategy;
import org.key_project.prover.strategy.IFormulaTermFeatures;
import org.key_project.prover.strategy.IntegerStrategy;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.RuleSetDispatchFeature;
import org.key_project.prover.strategy.costbased.feature.SumFeature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

import org.jspecify.annotations.NonNull;


/// This strategy implements reasoning for integer arithmetics. In particular,
/// it supports linear integer arithmetics via Gaussian elimination,
/// Fourier-Motzkin; and non-linear integer reasoning via cross-multiplication
/// and Gröbner basis.
///
/// Do not create directly, instead use [IntegerStrategyFactory].
public class JavaIntegerStrategy extends IntegerStrategy<Goal> implements ComponentStrategy<Goal> {
    private final Proof proof;

    /// Caps how often a cross multiplication is applied on a branch.
    /// Justified by empirical measurements. Candidate to be exposed in
    /// a settings strategy pane (not the strategy pane)
    private static final int BRANCH_MULT_CAP = 8;

    public JavaIntegerStrategy(ArithTermFeatures tf, IFormulaTermFeatures ff, Proof proof,
            StrategyProperties strategyProperties) {
        super(tf, ff, StrategyProperties.NON_LIN_ARITH_COMPLETION.equals(
            strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY)),
            StrategyProperties.NON_LIN_ARITH_COMPLETION.equals(
                strategyProperties.getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY))
                    || StrategyProperties.NON_LIN_ARITH_DEF_OPS.equals(
                        strategyProperties
                                .getProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY)),
            strategyProperties.getProperty(StrategyProperties.STOPMODE_OPTIONS_KEY)
                    .equals(StrategyProperties.STOPMODE_NONCLOSE),
            new JavaFeatureConstants(), proof.getServices().getTypeConverter().getIntegerLDT());
        this.proof = proof;
        init();
    }

    @Override
    protected RuleSetDispatchFeature setupApprovalDispatcher() {
        final RuleSetDispatchFeature d = super.setupApprovalDispatcher();

        bindRuleSet(d, "defOps_jdiv", NonDuplicateAppModPositionFeature.INSTANCE);

        return d;
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
        super.setupDefOpsPrimaryCategories(d);
        if (arith == ArithTreatment.DEF_OPS) {
            bindRuleSet(d, "defOps_jdiv",
                SumFeature.createSum(NonDuplicateAppModPositionFeature.INSTANCE,
                    applyTF("divNum", tf.polynomial), applyTF("divDenom", tf.polynomial),
                    applyTF("divNum", tf.notContainsDivMod),
                    applyTF("divDenom", tf.notContainsDivMod),
                    ifZero(isBelow(ff.modalOperator()), longConst(200))));

            bindRuleSet(d, "defOps_jdiv_inline", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.polynomial), longConst(-5000)));
        } else {
            bindRuleSet(d, "defOps_jdiv", inftyConst());

            bindRuleSet(d, "defOps_jdiv_inline", add(applyTF("divNum", tf.literal),
                applyTF("divDenom", tf.literal), longConst(-4000)));
        }
    }

    @Override
    protected Feature getBranchCountFeatureFor(String prefix) {
        return BranchMultiplicationCountFeature.atMost(prefix, BRANCH_MULT_CAP);
    }

    @Override
    protected Feature createReducibleMonomialFeature(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return ReducibleMonomialsFeature.createReducible(dividend, divisor);
    }

    @Override
    protected Feature createTrivialMonomialLCRFeature(ProjectionToTerm<Goal> a,
            ProjectionToTerm<Goal> b) {
        return TrivialMonomialLCRFeature.create(a, b);
    }

    @Override
    protected ProjectionToTerm<Goal> createReduceMonomialsProjection(
            ProjectionToTerm<Goal> dividend, ProjectionToTerm<Goal> divisor) {
        return ReduceMonomialsProjection.create(dividend, divisor);
    }

    @Override
    protected ProjectionToTerm<Goal> createMonomialColumnOp(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        return MonomialColumnOp.create(leftCoefficient, polynomial);
    }

    @Override
    protected Feature createMonomialsSmallerThanFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right, IIntLdt numbers) {
        return MonomialsSmallerThanFeature.create(left, right, numbers);
    }

    @Override
    protected Feature createAtomSmallerThanFeature(String left, String right, IIntLdt numbers) {
        return AtomsSmallerThanFeature.create(instOf(left), instOf(right), numbers);
    }

    @Override
    protected ProjectionToTerm<Goal> createRoundingUpDividePolynomialsProjection(
            ProjectionToTerm<Goal> leftCoefficient, ProjectionToTerm<Goal> polynomial) {
        return DividePolynomialsProjection.createRoundingUp(leftCoefficient, polynomial);
    }

    @Override
    protected ProjectionToTerm<Goal> createRoundingDownDividePolynomialsProjection(
            ProjectionToTerm<Goal> leftCoefficient, ProjectionToTerm<Goal> polynomial) {
        return DividePolynomialsProjection.createRoundingDown(leftCoefficient, polynomial);
    }

    @Override
    protected ProjectionToTerm<Goal> createCoeffGcdProjection(ProjectionToTerm<Goal> monomialLeft,
            ProjectionToTerm<Goal> monomialRight) {
        return CoeffGcdProjection.create(monomialLeft, monomialRight);
    }

    @Override
    protected Feature createExactlyBoundedInEquationMultFeature(
            ProjectionToTerm<Goal> mult1Candidate, ProjectionToTerm<Goal> mult2Candidate,
            ProjectionToTerm<Goal> targetCandidate) {
        return InEquationMultFeature.exactlyBounded(mult1Candidate, mult2Candidate,
            targetCandidate);
    }

    @Override
    protected Feature createTotalyBoundedInEquationMultFeature(
            ProjectionToTerm<Goal> mult1Candidate, ProjectionToTerm<Goal> mult2Candidate,
            ProjectionToTerm<Goal> targetCandidate) {
        return InEquationMultFeature.totallyBounded(mult1Candidate, mult2Candidate,
            targetCandidate);
    }

    @Override
    protected Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.lt(left, right);
    }

    @Override
    protected Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right, ProjectionToTerm<Goal> leftCoeff,
            ProjectionToTerm<Goal> rightCoeff) {
        return PolynomialValuesCmpFeature.lt(left, right, leftCoeff, rightCoeff);
    }

    @Override
    protected Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.leq(left, right);
    }

    @Override
    protected Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right, ProjectionToTerm<Goal> leftCoeff,
            ProjectionToTerm<Goal> rightCoeff) {
        return PolynomialValuesCmpFeature.leq(left, right, leftCoeff, rightCoeff);
    }

    @Override
    protected Feature createEqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.eq(left, right);
    }

    @Override
    protected Feature createEqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right, ProjectionToTerm<Goal> leftCoeff,
            ProjectionToTerm<Goal> rightCoeff) {
        return PolynomialValuesCmpFeature.eq(left, right, leftCoeff, rightCoeff);
    }

    @Override
    protected Feature createDividesPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.divides(left, right);
    }

    @Override
    protected TermFeature createEqTermFeature(TermBuffer<Goal> t) {
        return EqTermFeature.create(t);
    }

    @Override
    protected Feature directlyBelowSymbolAtIndex(Operator symbol, int index) {
        return directlyBelowSymbolAtIndex(op(symbol), index);
    }

    protected Feature directlyBelowSymbolAtIndex(TermFeature symbolTF, int index) {
        final var oneUp = FocusProjection.create(1);
        if (index == -1) {
            return add(not(TopLevelFindFeature.ANTEC_OR_SUCC), applyTF(oneUp, symbolTF));
        }
        return add(not(TopLevelFindFeature.ANTEC_OR_SUCC),
            ifZero(applyTF(oneUp, symbolTF), eq(sub(oneUp, index), FocusProjection.INSTANCE),
                inftyConst()));
    }

    @Override
    protected TermGenerator<Goal> createMultiplesModEquationsGenerator(
            ProjectionToTerm<Goal> source, ProjectionToTerm<Goal> target) {
        return MultiplesModEquationsGenerator.create(source, target);
    }

    @Override
    protected Term zTerm(String num) {
        return proof.getServices().getTermBuilder().zTerm(num);
    }

    @Override
    protected ProjectionToTerm<Goal> opTerm(Operator op, ProjectionToTerm<Goal> subTerm0,
            ProjectionToTerm<Goal> subTerm1) {
        return TermConstructionProjection.create(op, new ProjectionToTerm[] { subTerm0, subTerm1 });
    }

    @Override
    protected Feature createTermSmallerThanFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return TermSmallerThanFeature.create(left, right);
    }

    @Override
    protected Feature createMonomialSmallerThan(String left, String right, IIntLdt numbers) {
        return MonomialsSmallerThanFeature.create(instOf(left), instOf(right), numbers);
    }

    @Override
    protected TermGenerator<Goal> createRootsGenerator(ProjectionToTerm<Goal> powerRelation) {
        return RootsGenerator.create(powerRelation, proof.getServices());
    }

    @Override
    protected Operator or() {
        return Junctor.OR;
    }

    @Override
    protected Operator and() {
        return Junctor.AND;
    }

    @Override
    protected TermGenerator<Goal> upwardsWithIndexSuperGenerator(TermFeature cond) {
        return SuperTermGenerator.upwardsWithIndex(cond, proof.getServices());
    }

    @Override
    protected RuleSet getHeuristic(String p_name) {
        final NamespaceSet nss = proof.getNamespaces();
        final Namespace<@NonNull RuleSet> ns = nss.ruleSets();
        final RuleSet h = ns.lookup(new Name(p_name));

        assert h != null : "Did not find the rule set " + p_name;

        return h;
    }

    @Override
    protected Feature isBelow(TermFeature t) {
        final de.uka.ilkd.key.strategy.termProjection.TermBuffer superTerm =
            new de.uka.ilkd.key.strategy.termProjection.TermBuffer();
        return not(sum(superTerm, SuperTermGenerator.upwards(any(), proof.getServices()),
            not(applyTF(superTerm, t))));
    }

    @Override
    public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
        return null;
    }
}
