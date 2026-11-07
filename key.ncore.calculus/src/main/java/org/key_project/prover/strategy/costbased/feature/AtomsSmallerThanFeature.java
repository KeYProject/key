/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import org.key_project.ldt.IIntLdt;
import org.key_project.logic.Term;
import org.key_project.logic.TermOrdering;
import org.key_project.logic.op.Function;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;


/**
 * Feature that returns zero iff each variable/atom of one monomial is smaller than all variables of
 * a second monomial.
 *
 * <p>
 * The value is determined by the compared instantiation terms alone: the atom ordering consists
 * of the number-literal distinction, the term-only {@link TermOrdering},
 * and the introduction time of definitional skolem symbols, which is a constant of the symbol
 * (see {@link AbstractMonomialSmallerThanFeature#introductionTime}). Hence {@link StableCost} --
 * the same classification, for the same reason, as {@link MonomialsSmallerThanFeature}, which
 * orders whole monomials by the same ingredients.
 * </p>
 */
@StableCost
public class AtomsSmallerThanFeature<GOAL extends ProofGoal<GOAL>>
        extends AbstractMonomialSmallerThanFeature<GOAL> {

    private final ProjectionToTerm left, right;
    private final Function Z;

    private AtomsSmallerThanFeature(ProjectionToTerm left, ProjectionToTerm right,
            TermOrdering termOrdering, IIntLdt numbers) {
        super(termOrdering, numbers);
        this.left = left;
        this.right = right;
        this.Z = numbers.getNumberSymbol();
    }


    public static <GOAL extends ProofGoal<GOAL>> Feature create(ProjectionToTerm left,
            ProjectionToTerm right,
            TermOrdering termOrdering, IIntLdt numbers) {
        return new AtomsSmallerThanFeature<>(left, right, termOrdering, numbers);
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos,
            GOAL goal, MutableState mState) {
        final Term leftTerm = left.toTerm(app, pos, goal, mState);
        final Term rightTerm = right.toTerm(app, pos, goal, mState);
        assert leftTerm != null && rightTerm != null
                : "@AssumeAssertion(nullness): Instantiations should not be null";
        return lessThan(collectAtoms(leftTerm), collectAtoms(rightTerm), pos, goal);
    }

    /**
     * this overwrites the method of <code>SmallerThanFeature</code>
     */
    @Override
    protected boolean lessThan(Term t1, Term t2, PosInOccurrence focus, GOAL goal) {
        if (t1.op() == Z) {
            if (t2.op() != Z) {
                return true;
            }
            return super.lessThan(t1, t2, focus, goal);
        } else {
            if (t2.op() == Z) {
                return false;
            }
        }

        final int v = introductionTime(t2.op()) - introductionTime(t1.op());
        if (v < 0) {
            return true;
        }
        if (v > 0) {
            return false;
        }

        return super.lessThan(t1, t2, focus, goal);
    }
}
