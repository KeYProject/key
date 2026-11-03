/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.op.Operator;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public interface FeatureConstants<G extends ProofGoal<G>> {
    Feature nonDuplicateAppModPositionFeature();

    Feature notInScopeOfModalityFeature();

    Feature topLevelFindSucc();

    Feature checkApplyEqFeature();

    Feature findRightishFeature(IIntLdt numbers, Operator equals);

    Feature createReducibleMonomialFeature(ProjectionToTerm<G> dividend,
                                           ProjectionToTerm<G> divisor);
}
