/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.JMonomial;
import de.uka.ilkd.key.strategy.StaticFeatureCollection;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.EqTermFeature;
import de.uka.ilkd.key.strategy.termgenerator.MultiplesModEquationsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.RootsGenerator;
import de.uka.ilkd.key.strategy.termgenerator.SuperTermGenerator;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.FeatureConstants;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

import org.jspecify.annotations.NullMarked;

import static org.key_project.prover.strategy.StaticFeatureCollection.op;

@NullMarked
public class JavaFeatureConstants implements FeatureConstants<Goal> {
    @Override
    public Feature nonDuplicateAppModPositionFeature() {
        return NonDuplicateAppModPositionFeature.INSTANCE;
    }

    @Override
    public Feature notInScopeOfModalityFeature() {
        return NotInScopeOfModalityFeature.INSTANCE;
    }

    @Override
    public Feature topLevelFindSucc() {
        return TopLevelFindFeature.SUCC;
    }

    @Override
    public Feature checkApplyEqFeature() {
        return CheckApplyEqFeature.INSTANCE;
    }

    @Override
    public Feature findRightishFeature(IIntLdt numbers, Operator equals) {
        return FindRightishFeature.create(numbers, equals);
    }

    @Override
    public Feature createReducibleMonomialFeature(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return ReducibleMonomialsFeature.createReducible(dividend, divisor, JMonomial::create);
    }

    @Override
    public Feature createTrivialMonomialLCRFeature(ProjectionToTerm<Goal> a,
            ProjectionToTerm<Goal> b) {
        return TrivialMonomialLCRFeature.create(a, b, JMonomial::create);
    }

    @Override
    public ProjectionToTerm<Goal> createReduceMonomialsProjection(
            ProjectionToTerm<Goal> dividend, ProjectionToTerm<Goal> divisor) {
        return ReduceMonomialsProjection.create(dividend, divisor);
    }

    @Override
    public ProjectionToTerm<Goal> createMonomialColumnOp(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        return MonomialColumnOp.create(leftCoefficient, polynomial);
    }

    @Override
    public ProjectionToTerm<Goal> createRoundingUpDividePolynomialsProjection(
            ProjectionToTerm<Goal> leftCoefficient, ProjectionToTerm<Goal> polynomial) {
        return DividePolynomialsProjection.createRoundingUp(leftCoefficient, polynomial);
    }

    @Override
    public ProjectionToTerm<Goal> createRoundingDownDividePolynomialsProjection(
            ProjectionToTerm<Goal> leftCoefficient, ProjectionToTerm<Goal> polynomial) {
        return DividePolynomialsProjection.createRoundingDown(leftCoefficient, polynomial);
    }

    @Override
    public ProjectionToTerm<Goal> createCoeffGcdProjection(ProjectionToTerm<Goal> monomialLeft,
            ProjectionToTerm<Goal> monomialRight) {
        return CoeffGcdProjection.create(monomialLeft, monomialRight);
    }

    @Override
    public Feature createExactlyBoundedInEquationMultFeature(
            ProjectionToTerm<Goal> mult1Candidate, ProjectionToTerm<Goal> mult2Candidate,
            TermFeature targetCandidate) {
        return new IsBoundedByInequationFeature<>(mult1Candidate, mult2Candidate,
            targetCandidate, JMonomial::create);
    }

    @Override
    public Feature createTotalyBoundedInEquationMultFeature(
            ProjectionToTerm<Goal> mult1Candidate, ProjectionToTerm<Goal> mult2Candidate,
            ProjectionToTerm<Goal> targetCandidate) {
        return InEquationMultFeature.totallyBounded(mult1Candidate, mult2Candidate,
            targetCandidate, JMonomial::create);
    }

    @Override
    public Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.lt(left, right);
    }

    @Override
    public Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right, ProjectionToTerm<Goal> leftCoeff,
            ProjectionToTerm<Goal> rightCoeff) {
        return PolynomialValuesCmpFeature.lt(left, right, leftCoeff, rightCoeff);
    }

    @Override
    public Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.leq(left, right);
    }

    @Override
    public Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right, ProjectionToTerm<Goal> leftCoeff,
            ProjectionToTerm<Goal> rightCoeff) {
        return PolynomialValuesCmpFeature.leq(left, right, leftCoeff, rightCoeff);
    }

    @Override
    public Feature createEqPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.eq(left, right);
    }

    @Override
    public Feature createDividesPolynomialValuesCmpFeature(ProjectionToTerm<Goal> left,
            ProjectionToTerm<Goal> right) {
        return PolynomialValuesCmpFeature.divides(left, right);
    }

    @Override
    public TermFeature createEqTermFeature(TermBuffer<Goal> t) {
        return EqTermFeature.create(t);
    }

    @Override
    public Feature directlyBelowSymbolAtIndex(Operator symbol, int index) {
        return StaticFeatureCollection.directlyBelowSymbolAtIndex(op(symbol), index);
    }

    @Override
    public TermGenerator<Goal> createMultiplesModEquationsGenerator(
            ProjectionToTerm<Goal> source, ProjectionToTerm<Goal> target) {
        return MultiplesModEquationsGenerator.create(source, target);
    }

    @Override
    public ProjectionToTerm<Goal> opTerm(Operator op, ProjectionToTerm<Goal> subTerm0,
            ProjectionToTerm<Goal> subTerm1) {
        return TermConstructionProjection.create(op, new ProjectionToTerm[] { subTerm0, subTerm1 });
    }

    @Override
    public TermGenerator<Goal> createRootsGenerator(ProjectionToTerm<Goal> powerRelation,
            LogicServices services) {
        return RootsGenerator.create(powerRelation, (TermServices) services);
    }

    @Override
    public TermGenerator<Goal> upwardsWithIndexSuperGenerator(TermFeature cond,
            LogicServices services) {
        return SuperTermGenerator.upwardsWithIndex(cond, (Services) services);
    }
}
