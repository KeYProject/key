/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import org.key_project.logic.LogicServices;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.quantifierHeuristics.TriggerTreatment;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.prover.strategy.costbased.termProjection.TermBuffer;
import org.key_project.prover.strategy.costbased.termfeature.TermFeature;
import org.key_project.prover.strategy.costbased.termgenerator.TermGenerator;

/// Features that are required for the [IntegerStrategy] and [FOLStrategy] but
/// are language-dependent and need to be defined for JavaKeY, RustyKeY, etc.
public interface FeatureConstants {
    Feature nonDuplicateAppModPositionFeature();

    Feature notInScopeOfModalityFeature();

    Feature topLevelFindAntecOrSuccWithUpdate();

    Feature topLevelFindAntec();

    Feature topLevelFindSucc();

    Feature checkApplyEqFeature();

    TermFeature createEliminableQuantifier();

    TermFeature createEqTermFeature(TermBuffer t);

    Feature directlyBelowSymbolAtIndex(Operator symbol, int index);

    ProjectionToTerm opTerm(Operator op, ProjectionToTerm subTerm0,
            ProjectionToTerm subTerm1);

    TermGenerator upwardsWithIndexSuperGenerator(TermFeature cond, LogicServices services);

    Feature eqNonDuplicateAppFeature();

    Feature splittableQuantifiedFormula();

    TermGenerator createTriggeredInstantiations(boolean skipConditions);

    Feature diffFindAndReplacewithFeature();

    Feature countMaxDPath();

    Feature purePosDPath();

    Feature countPosDPath();

    TermGenerator allowedCutPositionsGenerator();

    Feature allowedCutPositions();

    TermFeature selectSkolemConstant();

    Feature countOccurrences(ProjectionToTerm target);

    TermFeature containsExecutableCodeTF();

    TermGenerator heuristicGenerator(TriggerTreatment option);

    Feature computeInstantiationCostOf(ProjectionToTerm instOfT,
            TriggerTreatment triggerTreatment);

    Feature getInstantiationTieBreakFeature(TermBuffer varInst, String s);
}
