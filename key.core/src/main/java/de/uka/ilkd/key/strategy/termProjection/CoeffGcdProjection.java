/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.metaconstruct.arith.JMonomial;
import de.uka.ilkd.key.rule.metaconstruct.arith.JPolynomial;

import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Monomial;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Polynomial;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Given a monomial and a polynomial, this projection computes the gcd of all numerical
 * coefficients. The constant term of the polynomial is ignored. The result is guaranteed to be
 * non-negative.
 */
@StableCost
public class CoeffGcdProjection implements ProjectionToTerm {

    private final ProjectionToTerm monomialLeft;
    private final ProjectionToTerm polynomialRight;

    private CoeffGcdProjection(ProjectionToTerm monomialLeft,
            ProjectionToTerm polynomialRight) {
        this.monomialLeft = monomialLeft;
        this.polynomialRight = polynomialRight;
    }

    public static ProjectionToTerm create(ProjectionToTerm monomialLeft,
            ProjectionToTerm polynomialRight) {
        return new CoeffGcdProjection(monomialLeft, polynomialRight);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, ProofGoal<?> goal, MutableState mState) {
        final Services services = ((Proof) goal.proof()).getServices();

        final Term monoT = monomialLeft.toTerm(app, pos, goal, mState);
        final Term polyT = polynomialRight.toTerm(app, pos, goal, mState);

        final Monomial mono = JMonomial.create(monoT, services);
        final Polynomial poly = JPolynomial.create(polyT, services);

        final BigInteger gcd = mono.getCoefficient().gcd(poly.coeffGcd());
        return services.getTermBuilder().zTerm(gcd.abs().toString());
    }
}
