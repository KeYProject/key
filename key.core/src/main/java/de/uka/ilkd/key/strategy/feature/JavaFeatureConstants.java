/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.equality.RenamingTermProperty;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.strategy.StaticFeatureCollection;
import de.uka.ilkd.key.strategy.quantifierHeuristics.EliminableQuantifierTF;
import de.uka.ilkd.key.strategy.quantifierHeuristics.HeuristicInstantiation;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationCost;
import de.uka.ilkd.key.strategy.quantifierHeuristics.InstantiationTieBreakFeature;
import de.uka.ilkd.key.strategy.quantifierHeuristics.SplittableQuantifiedFormulaFeature;
import de.uka.ilkd.key.strategy.termProjection.*;
import de.uka.ilkd.key.strategy.termfeature.ContainsExecutableCodeTermFeature;
import de.uka.ilkd.key.strategy.termgenerator.*;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.FeatureConstants;
import org.key_project.prover.strategy.costbased.feature.*;
import org.key_project.prover.strategy.costbased.quantifierHeuristics.TriggerTreatment;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.EqTermFeature;
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
    public Feature eqNonDuplicateAppFeature() {
        return EqNonDuplicateAppFeature.INSTANCE;
    }

    @Override
    public Feature notInScopeOfModalityFeature() {
        return NotInScopeOfModalityFeature.INSTANCE;
    }

    @Override
    public Feature topLevelFindAntecOrSuccWithUpdate() {
        return TopLevelFindFeature.ANTEC_OR_SUCC_WITH_UPDATE;
    }

    @Override
    public Feature topLevelFindAntecOrSucc() {
        return TopLevelFindFeature.ANTEC_OR_SUCC;
    }

    @Override
    public Feature topLevelFindAntec() {
        return TopLevelFindFeature.ANTEC;
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
    public ProjectionToTerm createReduceMonomialsProjection(
            ProjectionToTerm dividend, ProjectionToTerm divisor) {
        return ReduceMonomialsProjection.create(dividend, divisor);
    }

    @Override
    public ProjectionToTerm createMonomialColumnOp(ProjectionToTerm leftCoefficient,
            ProjectionToTerm polynomial) {
        return MonomialColumnOp.create(leftCoefficient, polynomial);
    }

    @Override
    public ProjectionToTerm createRoundingUpDividePolynomialsProjection(
            ProjectionToTerm leftCoefficient, ProjectionToTerm polynomial) {
        return DividePolynomialsProjection.createRoundingUp(leftCoefficient, polynomial);
    }

    @Override
    public ProjectionToTerm createRoundingDownDividePolynomialsProjection(
            ProjectionToTerm leftCoefficient, ProjectionToTerm polynomial) {
        return DividePolynomialsProjection.createRoundingDown(leftCoefficient, polynomial);
    }

    @Override
    public ProjectionToTerm createCoeffGcdProjection(ProjectionToTerm monomialLeft,
            ProjectionToTerm monomialRight) {
        return CoeffGcdProjection.create(monomialLeft, monomialRight);
    }

    @Override
    public Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right) {
        return PolynomialValuesCmpFeature.lt(left, right);
    }

    @Override
    public Feature createLtPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right, ProjectionToTerm leftCoeff,
            ProjectionToTerm rightCoeff) {
        return PolynomialValuesCmpFeature.lt(left, right, leftCoeff, rightCoeff);
    }

    @Override
    public Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right) {
        return PolynomialValuesCmpFeature.leq(left, right);
    }

    @Override
    public Feature createLeqPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right, ProjectionToTerm leftCoeff,
            ProjectionToTerm rightCoeff) {
        return PolynomialValuesCmpFeature.leq(left, right, leftCoeff, rightCoeff);
    }

    @Override
    public Feature createEqPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right) {
        return PolynomialValuesCmpFeature.eq(left, right);
    }

    @Override
    public Feature createDividesPolynomialValuesCmpFeature(ProjectionToTerm left,
            ProjectionToTerm right) {
        return PolynomialValuesCmpFeature.divides(left, right);
    }

    @Override
    public TermFeature createEqTermFeature(TermBuffer t) {
        return EqTermFeature.create(t, RenamingTermProperty.RENAMING_TERM_PROPERTY);
    }

    @Override
    public Feature directlyBelowSymbolAtIndex(Operator symbol, int index) {
        return StaticFeatureCollection.directlyBelowSymbolAtIndex(op(symbol), index);
    }

    @Override
    public TermGenerator<Goal> createMultiplesModEquationsGenerator(
            ProjectionToTerm source, ProjectionToTerm target) {
        return MultiplesModEquationsGenerator.create(source, target);
    }

    @Override
    public ProjectionToTerm opTerm(Operator op, ProjectionToTerm subTerm0,
            ProjectionToTerm subTerm1) {
        return TermConstructionProjection.create(op, new ProjectionToTerm[] { subTerm0, subTerm1 });
    }

    @Override
    public TermGenerator<Goal> createRootsGenerator(ProjectionToTerm powerRelation,
            LogicServices services) {
        return RootsGenerator.create(powerRelation, (TermServices) services);
    }

    @Override
    public TermGenerator<Goal> upwardsWithIndexSuperGenerator(TermFeature cond,
            LogicServices services) {
        return SuperTermGenerator.upwardsWithIndex(cond, (Services) services);
    }

    @Override
    public TermFeature createEliminableQuantifier() {
        return EliminableQuantifierTF.INSTANCE;
    }

    @Override
    public Feature splittableQuantifiedFormula() {
        return SplittableQuantifiedFormulaFeature.INSTANCE;
    }

    @Override
    public TermGenerator<Goal> createTriggeredInstantiations(boolean skipConditions) {
        return TriggeredInstantiations.create(skipConditions);
    }

    @Override
    public TermGenerator<Goal> superTermGenerator(TermFeature cond, LogicServices services) {
        return SuperTermGenerator.upwards(cond, (Services) services);
    }

    @Override
    public Feature diffFindAndReplacewithFeature() {
        return DiffFindAndReplacewithFeature.INSTANCE;
    }

    @Override
    public Feature countMaxDPath() {
        return CountMaxDPathFeature.INSTANCE;
    }

    @Override
    public Feature countPosDPath() {
        return CountPosDPathFeature.INSTANCE;
    }

    @Override
    public Feature purePosDPath() {
        return PurePosDPathFeature.INSTANCE;
    }

    @Override
    public TermGenerator<Goal> allowedCutPositionsGenerator() {
        return AllowedCutPositionsGenerator.INSTANCE;
    }

    @Override
    public Feature allowedCutPositions() {
        return AllowedCutPositionFeature.INSTANCE;
    }

    @Override
    public TermFeature selectSkolemConstant() {
        return StaticFeatureCollection.selectSkolemConstantTermFeature();
    }

    @Override
    public Feature countOccurrences(ProjectionToTerm target) {
        return CountOccurrencesFeature.create(target, RenamingTermProperty.RENAMING_TERM_PROPERTY);
    }

    @Override
    public TermFeature containsExecutableCodeTF() {
        return ContainsExecutableCodeTermFeature.PROGRAMS;
    }

    @Override
    public TermGenerator<Goal> heuristicGenerator(TriggerTreatment option) {
        return HeuristicInstantiation.forOption(option);
    }

    @Override
    public Feature computeInstantiationCostOf(ProjectionToTerm instOf_t,
            TriggerTreatment option) {
        return InstantiationCost.create(instOf_t, option);
    }

    @Override
    public Feature getInstantiationTieBreakFeature(TermBuffer varInst, String s) {
        return InstantiationTieBreakFeature.create(varInst, s);
    }
}
