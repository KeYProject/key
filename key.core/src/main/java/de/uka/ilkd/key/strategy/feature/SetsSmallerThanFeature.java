/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.logic.op.ParametricFunctionInstance;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.SetTermFeatures;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;
import org.key_project.util.collection.ImmutableList;


public class SetsSmallerThanFeature extends SmallerThanFeature {

    private final ProjectionToTerm<Goal> left, right;
    private final SetTermFeatures setFeatures;


    private SetsSmallerThanFeature(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            SetTermFeatures setFeatures) {
        this.left = left;
        this.right = right;
        this.setFeatures = setFeatures;
    }


    public static Feature create(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            SetTermFeatures setFeatures) {
        return new SetsSmallerThanFeature(left, right, setFeatures);
    }


    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        final Term leftTerm = left.toTerm(app, pos, goal, mState);
        final Term rightTerm = right.toTerm(app, pos, goal, mState);

        return origLessThan(leftTerm, rightTerm, pos, goal);
    }


    protected boolean origLessThan(Term leftTerm, Term rightTerm, PosInOccurrence pos, Goal goal) {
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

        protected void collect(Term te) {
            if (te.op() instanceof ParametricFunctionInstance pfi
                    && (pfi.getBase() == setFeatures.union
                            || pfi.getBase() == setFeatures.intersect
                            || pfi.getBase() == setFeatures.disjoint)) {
                collect(te.sub(0));
                collect(te.sub(1));
            } else {
                addTerm(te);
            }
        }
    }

}
