/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

public interface FeatureConstants<G extends ProofGoal<G>> {
    Feature nonDuplicateAppModPositionFeature();

    Feature notInScopeOfModalityFeature();

    Feature topLevelFindSucc();

    Feature checkApplyEqFeature();

    Feature findRightishFeature(IIntLdt numbers, Operator equals);

    Feature createReducibleMonomialFeature(ProjectionToTerm<G> dividend,
            ProjectionToTerm<G> divisor);

    Feature createTrivialMonomialLCRFeature(ProjectionToTerm<G> a, ProjectionToTerm<G> b);

    ProjectionToTerm<G> createReduceMonomialsProjection(ProjectionToTerm<G> dividend,
            ProjectionToTerm<G> divisor);

    ProjectionToTerm<G> createMonomialColumnOp(ProjectionToTerm<G> leftCoefficient,
            ProjectionToTerm<G> polynomial);

    ProjectionToTerm<G> createRoundingUpDividePolynomialsProjection(
            ProjectionToTerm<G> leftCoefficient, ProjectionToTerm<G> polynomial);

    ProjectionToTerm<G> createRoundingDownDividePolynomialsProjection(
            ProjectionToTerm<G> leftCoefficient, ProjectionToTerm<G> polynomial);

    ProjectionToTerm<G> createCoeffGcdProjection(
            ProjectionToTerm<G> monomialLeft, ProjectionToTerm<G> monomialRight);

    Feature createExactlyBoundedInEquationMultFeature(
            ProjectionToTerm<G> mult1Candidate, ProjectionToTerm<G> mult2Candidate,
            TermFeature targetCandidate);

    Feature createTotalyBoundedInEquationMultFeature(
            ProjectionToTerm<G> mult1Candidate, ProjectionToTerm<G> mult2Candidate,
            ProjectionToTerm<G> targetCandidate);

    Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm<G> left,
            ProjectionToTerm<G> right);

    Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm<G> left,
            ProjectionToTerm<G> right, ProjectionToTerm<G> leftCoeff,
            ProjectionToTerm<G> rightCoeff);

    Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm<G> left,
            ProjectionToTerm<G> right);

    Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm<G> left,
            ProjectionToTerm<G> right, ProjectionToTerm<G> leftCoeff,
            ProjectionToTerm<G> rightCoeff);

    Feature createEqPolynomialValuesCmpFeature(ProjectionToTerm<G> left,
            ProjectionToTerm<G> right);

    Feature createDividesPolynomialValuesCmpFeature(ProjectionToTerm<G> left,
            ProjectionToTerm<G> right);

    TermFeature createEqTermFeature(TermBuffer<G> t);

    Feature directlyBelowSymbolAtIndex(Operator symbol, int index);

    TermGenerator<G> createMultiplesModEquationsGenerator(
            ProjectionToTerm<G> source, ProjectionToTerm<G> target);

    ProjectionToTerm<G> opTerm(Operator op, ProjectionToTerm<G> subTerm0,
            ProjectionToTerm<G> subTerm1);

    TermGenerator<G> createRootsGenerator(ProjectionToTerm<G> powerRelation,
            LogicServices services);

    TermGenerator<G> upwardsWithIndexSuperGenerator(TermFeature cond, LogicServices services);
}
