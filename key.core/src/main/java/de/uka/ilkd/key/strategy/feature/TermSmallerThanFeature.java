/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

/**
 * Feature that returns zero iff one term is smaller than another term in the current term ordering
 */
public class TermSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;

    public static Feature create(ProjectionToTerm left, ProjectionToTerm right) {
        return new TermSmallerThanFeature(left, right);
    }

    private TermSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right) {
        this.left = left;
        this.right = right;
    }

    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal) {
        return lessThan(left.toTerm(app, pos, goal), right.toTerm(app, pos, goal), pos, goal);
    }

}
