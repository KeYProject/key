/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

import org.key_project.logic.sort.Sort;

public class ImplicitCastNecessary extends BinaryFeature {

    private final ProjectionToTerm projection;

    private ImplicitCastNecessary(ProjectionToTerm projection) {
        this.projection = projection;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null && pos.depth() >= 1;

        int subPos = pos.getIndex();

        final Sort maxSort = TermHelper.getMaxSort(pos.up().subTerm(), subPos);
        return projection.toTerm(app, pos, goal, mState).sort().extendsTrans(maxSort);
    }

    public static Feature create(ProjectionToTerm s1) {
        return new ImplicitCastNecessary(s1);
    }

}
