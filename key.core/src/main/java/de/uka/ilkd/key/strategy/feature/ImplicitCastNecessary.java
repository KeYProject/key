/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.util.TermHelper;
import de.uka.ilkd.key.proof.Goal;

import org.key_project.logic.sort.Sort;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public class ImplicitCastNecessary extends BinaryFeature {

    private final ProjectionToTerm<Goal> projection;

    private ImplicitCastNecessary(ProjectionToTerm<Goal> projection) {
        this.projection = projection;
    }

    protected boolean filter(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        assert pos != null && pos.depth() >= 1;

        int subPos = pos.getIndex();

        final Sort maxSort = TermHelper.getMaxSort((Term) pos.up().subTerm(), subPos);
        return projection.toTerm(app, pos, goal, mState).sort().extendsTrans(maxSort);
    }

    public static Feature<Goal> create(ProjectionToTerm<Goal> s1) {
        return new ImplicitCastNecessary(s1);
    }

}
