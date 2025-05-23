/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Feature that decides whether the multiplication of two inequations (using rules of set
 * inEqSimp_nonLin_multiply) is allowed. We only do this if the product of the left sides of the
 * inequations has factors in common with the left side of some other inequation, similarly to how
 * it is decided in the Buchberger algorithm.
 */
public abstract class InEquationMultFeature extends BinaryTacletAppFeature {

    protected final ProjectionToTerm<Goal> targetCandidate;
    protected final ProjectionToTerm<Goal> mult1Candidate;
    protected final ProjectionToTerm<Goal> mult2Candidate;

    /**
     * Return zero iff the multiplication of mult1 and mult2 is allowed, because the resulting
     * product is partially covered by target.
     *
     * @param mult1Candidate the left side of the first inequation to be multiplied
     * @param mult2Candidate the left side of the second inequation to be multiplied
     * @param targetCandidate the left side of the inequation that is supposed to bound the other
     *        two inequations
     */
    public static Feature partiallyBounded(ProjectionToTerm<Goal> mult1Candidate,
            ProjectionToTerm<Goal> mult2Candidate, ProjectionToTerm<Goal> targetCandidate) {
        return new InEquationMultFeature(mult1Candidate, mult2Candidate, targetCandidate) {
            @Override
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return !mult2M.reduce(targetM).variablesDisjoint(mult1M)
                        && !mult1M.reduce(targetM).variablesDisjoint(mult2M);
            }
        };
    }

    /**
     * Return zero iff the product of mult1 and mult2 is a factor of target
     */
    public static Feature totallyBounded(ProjectionToTerm<Goal> mult1Candidate,
            ProjectionToTerm<Goal> mult2Candidate, ProjectionToTerm<Goal> targetCandidate) {
        return new InEquationMultFeature(mult1Candidate, mult2Candidate, targetCandidate) {
            @Override
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return targetM.variablesSubsume(mult1M.multiply(mult2M));
            }
        };
    }

    /**
     * Return zero iff the product of mult1 and mult2 is target
     */
    public static Feature exactlyBounded(ProjectionToTerm<Goal> mult1Candidate,
            ProjectionToTerm<Goal> mult2Candidate, ProjectionToTerm<Goal> targetCandidate) {
        return new InEquationMultFeature(mult1Candidate, mult2Candidate, targetCandidate) {
            @Override
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return targetM.variablesEqual(mult1M.multiply(mult2M));
            }
        };
    }

    protected InEquationMultFeature(ProjectionToTerm<Goal> mult1Candidate,
            ProjectionToTerm<Goal> mult2Candidate, ProjectionToTerm<Goal> targetCandidate) {
        this.mult1Candidate = mult1Candidate;
        this.mult2Candidate = mult2Candidate;
        this.targetCandidate = targetCandidate;
    }

    @Override
    protected final boolean filter(TacletApp app, PosInOccurrence pos, Goal goal,
            MutableState mState) {
        final Services services = goal.proof().getServices();
        final Monomial targetM =
            Monomial.create(targetCandidate.toTerm(app, pos, goal, mState), services);
        final Monomial mult1M =
            Monomial.create(mult1Candidate.toTerm(app, pos, goal, mState), services);
        final Monomial mult2M =
            Monomial.create(mult2Candidate.toTerm(app, pos, goal, mState), services);

        return filter(targetM, mult1M, mult2M);
    }

    protected abstract boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M);
}
