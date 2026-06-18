/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Feature that returns zero iff one term is smaller than another term in the current term ordering
 */
public class TermSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm<Goal> left, right;

    public static Feature create(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return new TermSmallerThanFeature(left, right);
    }

    private TermSmallerThanFeature(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        this.left = left;
        this.right = right;
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return lessThan(left.toTerm(app, pos, goal, mState),
            right.toTerm(app, pos, goal, mState),
            pos, goal);
    }

}
