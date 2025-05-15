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
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;


/**
 * Return zero iff the monomial <code>dividendSV</code> can be made smaller (in the polynomial
 * reduction ordering) by adding or subtracting <code>divisorSV</code>
 */
public abstract class ReducibleMonomialsFeature extends BinaryTacletAppFeature {
    private final ProjectionToTerm<Goal> dividend, divisor;

    private ReducibleMonomialsFeature(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        this.dividend = dividend;
        this.divisor = divisor;
    }

    public static Feature createReducible(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return new ReducibleMonomialsFeature(dividend, divisor) {
            @Override
            protected boolean checkReducibility(Monomial mDividend, Monomial mDivisor) {
                return mDivisor.reducible(mDividend);
            }
        };
    }

    public static Feature createDivides(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return new ReducibleMonomialsFeature(dividend, divisor) {
            @Override
            protected boolean checkReducibility(Monomial mDividend, Monomial mDivisor) {
                return mDivisor.divides(mDividend);
            }
        };
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Term dividendT = dividend.toTerm(app, pos, goal, mState);
        final Term divisorT = divisor.toTerm(app, pos, goal, mState);

        final Services services = goal.proof().getServices();
        final Monomial mDividend = Monomial.create(dividendT, services);
        final Monomial mDivisor = Monomial.create(divisorT, services);

        return checkReducibility(mDividend, mDivisor);
    }

    protected abstract boolean checkReducibility(Monomial mDividend, Monomial mDivisor);
}
