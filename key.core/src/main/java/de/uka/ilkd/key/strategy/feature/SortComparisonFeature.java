/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

import org.key_project.logic.sort.Sort;

public class SortComparisonFeature extends BinaryFeature {

    public final static int SUBSORT = 0;

    public static Feature create(ProjectionToTerm s1, ProjectionToTerm s2, int cmp) {
        return new SortComparisonFeature(s1, s2, cmp);
    }

    private final ProjectionToTerm s1;
    private final ProjectionToTerm s2;
    private final int comparator;

    /**
     * creates a new comparison term feature
     */
    private SortComparisonFeature(ProjectionToTerm s1, ProjectionToTerm s2, int comparator) {
        this.s1 = s1;
        this.s2 = s2;
        this.comparator = comparator;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Sort sort1 = s1.toTerm(app, pos, goal, mState).sort();
        final Sort sort2 = s2.toTerm(app, pos, goal, mState).sort();

        return compare(sort1, sort2);
    }

    /**
     * @param sort1
     * @param sort2
     */
    protected boolean compare(final Sort sort1, final Sort sort2) {
        if (comparator == SUBSORT) {
            return sort1.extendsTrans(sort2);
        }
        return false;
    }

}
