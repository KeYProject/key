/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.TermOrdering;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.SmallerThanFeature;
import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Feature that returns zero iff one term is smaller than another term in the current term ordering
 */
@StableCost
public class TermSmallerThanFeature extends SmallerThanFeature<Goal> {

    private final ProjectionToTerm<Goal> left, right;

    public static Feature create(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            TermOrdering termOrdering) {
        return new TermSmallerThanFeature(left, right, termOrdering);
    }

    private TermSmallerThanFeature(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            TermOrdering termOrdering) {
        super(termOrdering);
        this.left = left;
        this.right = right;
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        return lessThan(left.toTerm(app, pos, goal, mState),
            right.toTerm(app, pos, goal, mState),
            pos, goal);
    }

}
