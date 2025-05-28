/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

import org.key_project.logic.Term;
import org.key_project.logic.op.Function;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public abstract class AbstractDividePolynomialsProjection implements ProjectionToTerm<Goal> {

    private final ProjectionToTerm leftCoefficient, polynomial;

    protected AbstractDividePolynomialsProjection(ProjectionToTerm leftCoefficient,
            ProjectionToTerm polynomial) {
        this.leftCoefficient = leftCoefficient;
        this.polynomial = polynomial;
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Term coeffT = leftCoefficient.toTerm(app, pos, goal, mState);
        final Term polyT = polynomial.toTerm(app, pos, goal, mState);

        final Services services = goal.proof().getServices();
        final BigInteger coeff =
            new BigInteger(AbstractTermTransformer.convertToDecimalString(coeffT, services));

        return quotient(coeff, polyT, services);
    }

    protected abstract Term divide(Monomial numerator, BigInteger denominator, Services services);

    private JTerm quotient(BigInteger monoCoeff, Term rightPoly,
            Services services) {
        final Function add = services.getTypeConverter().getIntegerLDT().getAdd();
        if (rightPoly.op() == add) {
            final var left = quotient(monoCoeff, rightPoly.sub(0), services);
            final var right = quotient(monoCoeff, rightPoly.sub(1), services);
            return services.getTermBuilder().func(add, left, right);
        }

        final Monomial rightMono = Monomial.create(rightPoly, services);
        return (JTerm) divide(rightMono, monoCoeff, services);
    }

}
