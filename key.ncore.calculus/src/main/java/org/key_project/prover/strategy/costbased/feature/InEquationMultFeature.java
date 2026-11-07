/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import java.util.function.BiFunction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Monomial;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Feature that decides whether the multiplication of two inequations (using rules of set
 * inEqSimp_nonLin_multiply) is allowed. We only do this if the product of the left sides of the
 * inequations has factors in common with the left side of some other inequation, similarly to how
 * it is decided in the Buchberger algorithm.
 */
public abstract class InEquationMultFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {

    protected final ProjectionToTerm targetCandidate;
    protected final ProjectionToTerm mult1Candidate;
    protected final ProjectionToTerm mult2Candidate;
    // creates a monomial from a given term
    protected final BiFunction<Term, LogicServices, Monomial> builder;

    /**
     * Return zero iff the multiplication of mult1 and mult2 is allowed, because the resulting
     * product is partially covered by target.
     *
     * @param mult1Candidate the left side of the first inequation to be multiplied
     * @param mult2Candidate the left side of the second inequation to be multiplied
     * @param targetCandidate the left side of the inequation that is supposed to bound the other
     *        two inequations
     */
    public static <GOAL extends ProofGoal<GOAL>> Feature partiallyBounded(
            ProjectionToTerm mult1Candidate,
            ProjectionToTerm mult2Candidate, ProjectionToTerm targetCandidate,
            BiFunction<Term, LogicServices, Monomial> builder) {
        return new InEquationMultFeature<GOAL>(mult1Candidate, mult2Candidate, targetCandidate,
            builder) {
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
    public static <GOAL extends ProofGoal<GOAL>> Feature totallyBounded(
            ProjectionToTerm mult1Candidate,
            ProjectionToTerm mult2Candidate, ProjectionToTerm targetCandidate,
            BiFunction<Term, LogicServices, Monomial> builder) {
        return new InEquationMultFeature<GOAL>(mult1Candidate, mult2Candidate, targetCandidate,
            builder) {
            @Override
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return targetM.variablesSubsume(mult1M.multiply(mult2M));
            }
        };
    }

    /**
     * Return zero iff the product of mult1 and mult2 is target
     */
    public static <GOAL extends ProofGoal<GOAL>> Feature exactlyBounded(
            ProjectionToTerm mult1Candidate,
            ProjectionToTerm mult2Candidate, ProjectionToTerm targetCandidate,
            BiFunction<Term, LogicServices, Monomial> builder) {
        return new InEquationMultFeature<GOAL>(mult1Candidate, mult2Candidate, targetCandidate,
            builder) {
            @Override
            protected boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M) {
                return targetM.variablesEqual(mult1M.multiply(mult2M));
            }
        };
    }

    protected InEquationMultFeature(ProjectionToTerm mult1Candidate,
            ProjectionToTerm mult2Candidate, ProjectionToTerm targetCandidate,
            BiFunction<Term, LogicServices, Monomial> builder) {
        this.mult1Candidate = mult1Candidate;
        this.mult2Candidate = mult2Candidate;
        this.targetCandidate = targetCandidate;
        this.builder = builder;
    }

    @Override
    protected final boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal,
            MutableState mState) {
        final LogicServices services = goal.proof().getServices();
        final Term target = targetCandidate.toTerm(app, pos, goal, mState);
        final Term mult1 = mult1Candidate.toTerm(app, pos, goal, mState);
        final Term mult2 = mult2Candidate.toTerm(app, pos, goal, mState);
        assert target != null && mult1 != null && mult2 != null
                : "@AssumeAssertion(nullness): instantiations should not be null";
        final Monomial targetM = builder.apply(target, services);
        final Monomial mult1M = builder.apply(mult1, services);
        final Monomial mult2M = builder.apply(mult2, services);

        return filter(targetM, mult1M, mult2M);
    }

    protected abstract boolean filter(Monomial targetM, Monomial mult1M, Monomial mult2M);
}
