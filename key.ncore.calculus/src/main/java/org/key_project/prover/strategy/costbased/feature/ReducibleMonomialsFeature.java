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
 * Return zero iff the monomial <code>dividend</code> can be made smaller (in the polynomial
 * reduction ordering) by adding or subtracting <code>divisor</code> ({@link #createReducible}), or
 * iff it is divided by it ({@link #createDivides}).
 */
@StableCost
public final class ReducibleMonomialsFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {
    /** Which monomial relation an instance checks. */
    private enum Check {
        REDUCIBLE, DIVIDES
    }

    private final ProjectionToTerm dividend, divisor;
    private final Check check;
    private final BiFunction<Term, LogicServices, Monomial> builder;

    private ReducibleMonomialsFeature(ProjectionToTerm dividend,
            ProjectionToTerm divisor, Check check,
            BiFunction<Term, LogicServices, Monomial> monBuilder) {
        this.dividend = dividend;
        this.divisor = divisor;
        this.check = check;
        this.builder = monBuilder;
    }

    /**
     * creates a feature that checks whether a monomial can be reduced by another one
     *
     * @param dividend the monomial that is queried for reducibility
     * @param divisor
     * @param monBuilder builder used to create a term from a monomial
     * @return
     * @param <GOAL>
     */
    public static <GOAL extends ProofGoal<GOAL>> Feature createReducible(
            ProjectionToTerm dividend,
            ProjectionToTerm divisor,
            BiFunction<Term, LogicServices, Monomial> monBuilder) {
        return new ReducibleMonomialsFeature<>(dividend, divisor, Check.REDUCIBLE, monBuilder);
    }

    /**
     * creates a feature that checks whether a monomial can be divided by another one
     *
     * @param dividend
     * @param divisor
     * @param monBuilder builder used to create a term from a monomial
     * @return
     * @param <GOAL>
     */
    public static <GOAL extends ProofGoal<GOAL>> Feature createDivides(
            ProjectionToTerm dividend,
            ProjectionToTerm divisor, BiFunction<Term, LogicServices, Monomial> monBuilder) {
        return new ReducibleMonomialsFeature<>(dividend, divisor, Check.DIVIDES, monBuilder);
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal, MutableState mState) {
        final Term dividendT = dividend.toTerm(app, pos, goal, mState);
        final Term divisorT = divisor.toTerm(app, pos, goal, mState);
        assert dividendT != null && divisorT != null
                : "@AssumeAssertion(nullness): Term should not be null";

        final LogicServices services = goal.proof().getServices();
        final Monomial mDividend = builder.apply(dividendT, services);
        final Monomial mDivisor = builder.apply(divisorT, services);

        return switch (check) {
            case REDUCIBLE -> mDivisor.reducible(mDividend);
            case DIVIDES -> mDivisor.divides(mDividend);
        };
    }
}
