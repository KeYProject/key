/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.Term;
import org.key_project.logic.TermOrdering;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Feature that returns zero iff one term is smaller than another term in the current term ordering
 */
@StableCost
public class TermSmallerThanFeature<GOAL extends ProofGoal<GOAL>> extends SmallerThanFeature<GOAL> {

    private final ProjectionToTerm<GOAL> left, right;

    public static <GOAL extends ProofGoal<GOAL>> Feature create(ProjectionToTerm<GOAL> left,
            ProjectionToTerm<GOAL> right,
            TermOrdering termOrdering) {
        return new TermSmallerThanFeature(left, right, termOrdering);
    }

    private TermSmallerThanFeature(ProjectionToTerm<GOAL> left, ProjectionToTerm<GOAL> right,
            TermOrdering termOrdering) {
        super(termOrdering);
        this.left = left;
        this.right = right;
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal, MutableState mState) {
        final Term leftTerm = left.toTerm(app, pos, goal, mState);
        final Term rightTerm = right.toTerm(app, pos, goal, mState);
        assert leftTerm != null && rightTerm != null
                : "@AssumeAssertion(nullness): Term should not be null";
        return lessThan(leftTerm, rightTerm, pos, goal);
    }

}
