/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;


/**
 * Return zero iff the monomial <code>dividend</code> can be made smaller (in the polynomial
 * reduction ordering) by adding or subtracting <code>divisor</code> ({@link #createReducible}), or
 * iff it is divided by it ({@link #createDivides}).
 */
@StableCost
public final class ReducibleMonomialsFeature extends BinaryTacletAppFeature {
    /** Which monomial relation an instance checks. */
    private enum Check {
        REDUCIBLE, DIVIDES
    }

    private final ProjectionToTerm<Goal> dividend, divisor;
    private final Check check;

    private ReducibleMonomialsFeature(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor, Check check) {
        this.dividend = dividend;
        this.divisor = divisor;
        this.check = check;
    }

    public static Feature createReducible(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return new ReducibleMonomialsFeature(dividend, divisor, Check.REDUCIBLE);
    }

    public static Feature createDivides(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return new ReducibleMonomialsFeature(dividend, divisor, Check.DIVIDES);
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Term dividendT = dividend.toTerm(app, pos, goal, mState);
        final Term divisorT = divisor.toTerm(app, pos, goal, mState);

        final Services services = goal.proof().getServices();
        final Monomial mDividend = Monomial.create(dividendT, services);
        final Monomial mDivisor = Monomial.create(divisorT, services);

        return switch (check) {
            case REDUCIBLE -> mDivisor.reducible(mDividend);
            case DIVIDES -> mDivisor.divides(mDividend);
        };
    }
}
