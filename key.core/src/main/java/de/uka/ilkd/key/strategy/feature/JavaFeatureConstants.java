/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import de.uka.ilkd.key.rule.metaconstruct.arith.JMonomial;
import org.key_project.ldt.IIntLdt;
import org.key_project.logic.op.Operator;
import org.key_project.prover.strategy.FeatureConstants;
import org.key_project.prover.strategy.costbased.feature.*;

import org.jspecify.annotations.NullMarked;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

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
}
