/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.strategy.termProjection.FocusFormulaProjection;
import de.uka.ilkd.key.strategy.termProjection.FocusProjection;

import org.key_project.ldt.IIntLdt;
import org.key_project.prover.strategy.FeatureConstants;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class JavaFeatureConstants implements FeatureConstants<Goal> {
    @Override
    public ProjectionToTerm<Goal> focusProjection() {
        return FocusProjection.INSTANCE;
    }

    @Override
    public ProjectionToTerm<Goal> focusProjection(int stepsUpwards) {
        return FocusProjection.create(stepsUpwards);
    }

    @Override
    public ProjectionToTerm<Goal> focusFormulaProjection() {
        return FocusFormulaProjection.INSTANCE;
    }

    @Override
    public Feature matchedAssumesFeature() {
        return MatchedAssumesFeature.INSTANCE;
    }

    @Override
    public Feature nonDuplicateAppModPositionFeature() {
        return NonDuplicateAppModPositionFeature.INSTANCE;
    }

    @Override
    public Feature notInScopeOfModalityFeature() {
        return NotInScopeOfModalityFeature.INSTANCE;
    }

    @Override
    public Feature diffFindAndIfFeature() {
        return DiffFindAndIfFeature.INSTANCE;
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
    public Feature findRightishFeature(IIntLdt numbers) {
        return FindRightishFeature.create(numbers);
    }
}
