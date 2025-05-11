/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;
import org.jspecify.annotations.NonNull;

public abstract class DividePolynomialsProjection extends AbstractDividePolynomialsProjection {

    private DividePolynomialsProjection(ProjectionToTerm leftCoefficient,
            ProjectionToTerm polynomial) {
        super(leftCoefficient, polynomial);
    }

    public static @NonNull ProjectionToTerm createRoundingDown(ProjectionToTerm leftCoefficient,
                                                               ProjectionToTerm polynomial) {
        return new DividePolynomialsProjection(leftCoefficient, polynomial) {
            protected @NonNull Term divide(@NonNull Monomial numerator, @NonNull BigInteger denominator, @NonNull Services services) {
                final BigInteger newRightCoeff = divide(numerator.getCoefficient(), denominator);
                return numerator.setCoefficient(newRightCoeff).toTerm(services);
            }

        };
    }

    public static @NonNull ProjectionToTerm createRoundingUp(ProjectionToTerm leftCoefficient,
                                                             ProjectionToTerm polynomial) {
        return new DividePolynomialsProjection(leftCoefficient, polynomial) {
            protected @NonNull Term divide(@NonNull Monomial numerator, @NonNull BigInteger denominator, @NonNull Services services) {
                final BigInteger newRightCoeff =
                    divide(numerator.getCoefficient().negate(), denominator).negate();
                return numerator.setCoefficient(newRightCoeff).toTerm(services);
            }
        };
    }

    protected @NonNull BigInteger divide(@NonNull BigInteger numerator, @NonNull BigInteger denominator) {
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
