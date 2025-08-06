/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public abstract class DividePolynomialsProjection extends AbstractDividePolynomialsProjection {

    private DividePolynomialsProjection(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        super(leftCoefficient, polynomial);
    }

    public static ProjectionToTerm<Goal> createRoundingDown(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        return new DividePolynomialsProjection(leftCoefficient, polynomial) {
            @Override
            protected Term divide(Monomial numerator, BigInteger denominator, Services services) {
                final BigInteger newRightCoeff = divide(numerator.getCoefficient(), denominator);
                return numerator.setCoefficient(newRightCoeff).toTerm(services);
            }

        };
    }

    public static ProjectionToTerm<Goal> createRoundingUp(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        return new DividePolynomialsProjection(leftCoefficient, polynomial) {
            @Override
            protected Term divide(Monomial numerator, BigInteger denominator,
                    Services services) {
                final BigInteger newRightCoeff =
                    divide(numerator.getCoefficient().negate(), denominator).negate();
                return numerator.setCoefficient(newRightCoeff).toTerm(services);
            }
        };
    }

    protected BigInteger divide(BigInteger numerator, BigInteger denominator) {
        final BigInteger remainder = numerator.remainder(denominator);

        BigInteger res = numerator.divide(denominator);
        if (remainder.signum() != 0 && numerator.signum() < 0) {
            if (denominator.signum() > 0) {
                res = res.subtract(BigInteger.ONE);
            } else {
                res = res.add(BigInteger.ONE);
            }
        }
        return res;
    }
}
