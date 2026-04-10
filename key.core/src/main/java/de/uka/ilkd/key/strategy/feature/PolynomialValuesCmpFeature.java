/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.feature;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.AbstractTermTransformer;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Polynomial;

import org.key_project.logic.Term;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.Feature;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Return zero only if the value of one (left) polynomial always will be (less or equal) or (less)
 * than the value of a second (right) polynomial. Both polynomials can optionally be multiplied with
 * some constant before comparison.
 */
public abstract class PolynomialValuesCmpFeature extends BinaryTacletAppFeature {

    private final ProjectionToTerm<Goal> left, right, leftCoeff, rightCoeff;

    protected PolynomialValuesCmpFeature(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        this.left = left;
        this.right = right;
        this.leftCoeff = leftCoeff;
        this.rightCoeff = rightCoeff;
    }

    public static Feature lt(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return lt(left, right, null, null);
    }

    public static Feature lt(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff) {
            @Override
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                return leftPoly.valueLess(rightPoly);
            }
        };
    }

    public static Feature leq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return leq(left, right, null, null);
    }

    public static Feature leq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff) {
            @Override
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                return leftPoly.valueLeq(rightPoly);
            }
        };
    }

    public static Feature eq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return eq(left, right, null, null);
    }

    public static Feature eq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff) {
            @Override
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                return leftPoly.valueEq(rightPoly);
            }
        };
    }

    public static Feature divides(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return divides(left, right, null, null);
    }

    public static Feature divides(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff) {
            @Override
            protected boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
                // we currently only support constant polynomials
                assert leftPoly.getParts().isEmpty();
                assert rightPoly.getParts().isEmpty();
                if (leftPoly.getConstantTerm().signum() == 0) {
                    return true;
                }
                if (rightPoly.getConstantTerm().signum() == 0) {
                    return false;
                }
                return leftPoly.getConstantTerm().mod(rightPoly.getConstantTerm().abs())
                        .signum() == 0;
            }
        };
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        return compare(getPolynomial(left, leftCoeff, app, pos, goal, mState),
            getPolynomial(right, rightCoeff, app, pos, goal, mState));
    }

    protected abstract boolean compare(Polynomial leftPoly, Polynomial rightPoly);

    private Polynomial getPolynomial(ProjectionToTerm<Goal> polyProj,
            ProjectionToTerm<Goal> coeffProj,
            TacletApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Services services = goal.proof().getServices();
        final Polynomial poly =
            Polynomial.create(polyProj.toTerm(app, pos, goal, mState), services);

        if (coeffProj == null) {
            return poly;
        }
        final Term coeffT = coeffProj.toTerm(app, pos, goal, mState);
        if (coeffT == null) {
            return poly;
        }

        final BigInteger coeff =
            new BigInteger(AbstractTermTransformer.convertToDecimalString(coeffT, services));
        return poly.multiply(coeff);
    }
}
