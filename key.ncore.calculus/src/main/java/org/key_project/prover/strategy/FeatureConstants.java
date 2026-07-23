/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy;

import org.key_project.ldt.IIntLdt;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public interface FeatureConstants<G extends ProofGoal<G>> {
    ProjectionToTerm<G> focusProjection();

    ProjectionToTerm<G> focusProjection(int stepsUpwards);

    ProjectionToTerm<G> focusFormulaProjection();

    Feature matchedAssumesFeature();

    Feature nonDuplicateAppModPositionFeature();

    Feature notInScopeOfModalityFeature();

    Feature diffFindAndIfFeature();

    Feature topLevelFindSucc();

    Feature checkApplyEqFeature();

    Feature findRightishFeature(IIntLdt numbers);
}
