/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.quantifierHeuristics.TriggerTreatment;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

public interface FeatureConstants<G extends ProofGoal<G>> {
    Feature nonDuplicateAppModPositionFeature();

    Feature notInScopeOfModalityFeature();

    Feature topLevelFindAntecOrSucc();

    Feature topLevelFindAntecOrSuccWithUpdate();

    Feature topLevelFindAntec();

    Feature topLevelFindSucc();

    Feature checkApplyEqFeature();

    TermFeature createEliminableQuantifier();

    ProjectionToTerm createReduceMonomialsProjection(ProjectionToTerm dividend,
            ProjectionToTerm divisor);

    ProjectionToTerm createMonomialColumnOp(ProjectionToTerm leftCoefficient,
            ProjectionToTerm polynomial);

    ProjectionToTerm createRoundingUpDividePolynomialsProjection(
            ProjectionToTerm leftCoefficient, ProjectionToTerm polynomial);

    ProjectionToTerm createRoundingDownDividePolynomialsProjection(
            ProjectionToTerm leftCoefficient, ProjectionToTerm polynomial);

    ProjectionToTerm createCoeffGcdProjection(
            ProjectionToTerm monomialLeft, ProjectionToTerm monomialRight);

    Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right);

    Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right, ProjectionToTerm leftCoeff,
            ProjectionToTerm rightCoeff);

    Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right);

    Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right, ProjectionToTerm leftCoeff,
            ProjectionToTerm rightCoeff);

    Feature createEqPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right);

    Feature createDividesPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right);

    TermFeature createEqTermFeature(TermBuffer t);

    Feature directlyBelowSymbolAtIndex(Operator symbol, int index);

    TermGenerator<G> createMultiplesModEquationsGenerator(
            ProjectionToTerm source, ProjectionToTerm target);

    ProjectionToTerm opTerm(Operator op, ProjectionToTerm subTerm0,
            ProjectionToTerm subTerm1);

    TermGenerator<G> createRootsGenerator(ProjectionToTerm powerRelation,
            LogicServices services);

    TermGenerator<G> upwardsWithIndexSuperGenerator(TermFeature cond, LogicServices services);

    Feature eqNonDuplicateAppFeature();

    Feature splittableQuantifiedFormula();

    TermGenerator<G> superTermGenerator(TermFeature cond, LogicServices services);

    TermGenerator<G> createTriggeredInstantiations(boolean skipConditions);

    Feature diffFindAndReplacewithFeature();

    Feature countMaxDPath();

    Feature purePosDPath();

    Feature countPosDPath();

    TermGenerator<G> allowedCutPositionsGenerator();

    Feature allowedCutPositions();

    TermFeature selectSkolemConstant();

    Feature countOccurrences(ProjectionToTerm target);

    TermFeature containsExecutableCodeTF();

    TermGenerator<G> heuristicGenerator(TriggerTreatment option);

    Feature computeInstantiationCostOf(ProjectionToTerm instOfT,
            TriggerTreatment triggerTreatment);

    Feature getInstantiationTieBreakFeature(TermBuffer varInst, String s);
}
