/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.ldt.LocSetLDT;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.termProjection.ProjectionToTerm;

import org.jspecify.annotations.NonNull;
import org.key_project.util.collection.ImmutableList;


public class SetsSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm left, right;
    private final LocSetLDT locSetLDT;


    private SetsSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right,
            LocSetLDT locSetLDT) {
        this.left = left;
        this.right = right;
        this.locSetLDT = locSetLDT;
    }


    public static @NonNull Feature create(ProjectionToTerm left, ProjectionToTerm right,
                                          LocSetLDT locSetLDT) {
        return new SetsSmallerThanFeature(left, right, locSetLDT);
    }


    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Term leftTerm = left.toTerm(app, pos, goal, mState);
        final Term rightTerm = right.toTerm(app, pos, goal, mState);

        return origLessThan(leftTerm, rightTerm, pos, goal);
    }


    protected boolean origLessThan(@NonNull Term leftTerm, @NonNull Term rightTerm, PosInOccurrence pos, Goal goal) {
        // TODO: Why is this method needed?
        final LiteralCollector m1 = new LiteralCollector();
        m1.collect(leftTerm);
        final ImmutableList<Term> literalsLeftTerm = m1.getResult();

        final LiteralCollector m2 = new LiteralCollector();
        m2.collect(rightTerm);
        final ImmutableList<Term> literalsRightTerm = m2.getResult();

        return super.lessThan(literalsLeftTerm, literalsRightTerm, pos, goal);
    }


    private class LiteralCollector extends Collector {

        protected void collect(@NonNull Term te) {
            final Operator op = te.op();
            if (op == locSetLDT.getUnion() || op == locSetLDT.getIntersect()
                    || op == locSetLDT.getDisjoint()) {
                collect(te.sub(0));
                collect(te.sub(1));
            } else {
                addTerm(te);
            }
        }
    }

}
