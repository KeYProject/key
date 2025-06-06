/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.logic.sort.Sort;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;

public class SortComparisonFeature<Goal extends ProofGoal<@NonNull Goal>>
        extends BinaryFeature {

    public final static int SUBSORT = 0;

    public static <Goal extends ProofGoal<@NonNull Goal>> Feature create(
            ProjectionToTerm<Goal> s1, ProjectionToTerm<Goal> s2, int cmp) {
        return new SortComparisonFeature<>(s1, s2, cmp);
    }

    private final ProjectionToTerm<Goal> s1;
    private final ProjectionToTerm<Goal> s2;
    private final int comparator;

    /// creates a new comparison term feature
    private SortComparisonFeature(ProjectionToTerm<Goal> s1, ProjectionToTerm<Goal> s2,
            int comparator) {
        this.s1 = s1;
        this.s2 = s2;
        this.comparator = comparator;
    }

    @Override
    protected <G extends ProofGoal<@NonNull G>> boolean filter(RuleApp app, PosInOccurrence pos,
            G goal, MutableState mState) {
        final Sort sort1 = s1.toTerm(app, pos, (Goal) goal, mState).sort();
        final Sort sort2 = s2.toTerm(app, pos, (Goal) goal, mState).sort();

        return compare(sort1, sort2);
    }

    /// @param sort1
    /// @param sort2
    protected boolean compare(final Sort sort1, final Sort sort2) {
        if (comparator == SUBSORT) {
            return sort1.extendsTrans(sort2);
        }
        return false;
    }

}
