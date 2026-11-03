/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.FeatureConstants;
import org.key_project.prover.strategy.costbased.feature.DiffFindAndAssumesFeature;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.FindRightishFeature;
import org.key_project.prover.strategy.costbased.feature.MatchedAssumesFeature;

import org.jspecify.annotations.NullMarked;

@NullMarked
public class JavaFeatureConstants implements FeatureConstants<Goal> {

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
        return DiffFindAndAssumesFeature.create();
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
}
