/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Given a monomial and a polynomial, this projection computes the gcd of all numerical
 * coefficients. The constant term of the polynomial is ignored. The result is guaranteed to be
 * non-negative.
 */
public class CoeffGcdProjection implements ProjectionToTerm<Goal> {

    private final ProjectionToTerm<Goal> monomialLeft;
    private final ProjectionToTerm<Goal> polynomialRight;

    private CoeffGcdProjection(ProjectionToTerm<Goal> monomialLeft,
            ProjectionToTerm<Goal> polynomialRight) {
        this.monomialLeft = monomialLeft;
        this.polynomialRight = polynomialRight;
    }

    public static ProjectionToTerm<Goal> create(ProjectionToTerm<Goal> monomialLeft,
            ProjectionToTerm<Goal> polynomialRight) {
        return new CoeffGcdProjection(monomialLeft, polynomialRight);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Services services = goal.proof().getServices();

        final Term monoT = monomialLeft.toTerm(app, pos, goal, mState);
        final Term polyT = polynomialRight.toTerm(app, pos, goal, mState);

        final Monomial mono = Monomial.create(monoT, services);
        final Polynomial poly = Polynomial.create(polyT, services);

        final BigInteger gcd = mono.getCoefficient().gcd(poly.coeffGcd());
        return services.getTermBuilder().zTerm(gcd.abs().toString());
    }
}
