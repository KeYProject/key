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
import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Return zero only if the value of one (left) polynomial always will be (less or equal) or (less)
 * than the value of a second (right) polynomial. Both polynomials can optionally be multiplied with
 * some constant before comparison.
 */
@StableCost
public final class PolynomialValuesCmpFeature extends BinaryTacletAppFeature {

    /** Which polynomial-value relation an instance checks. */
    private enum Cmp {
        LT, LEQ, EQ, DIVIDES
    }

    private final ProjectionToTerm<Goal> left, right, leftCoeff, rightCoeff;
    private final Cmp cmp;

    private PolynomialValuesCmpFeature(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff, Cmp cmp) {
        this.left = left;
        this.right = right;
        this.leftCoeff = leftCoeff;
        this.rightCoeff = rightCoeff;
        this.cmp = cmp;
    }

    public static Feature lt(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return lt(left, right, null, null);
    }

    public static Feature lt(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff, Cmp.LT);
    }

    public static Feature leq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return leq(left, right, null, null);
    }

    public static Feature leq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff, Cmp.LEQ);
    }

    public static Feature eq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return eq(left, right, null, null);
    }

    public static Feature eq(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff, Cmp.EQ);
    }

    public static Feature divides(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right) {
        return divides(left, right, null, null);
    }

    public static Feature divides(ProjectionToTerm<Goal> left, ProjectionToTerm<Goal> right,
            ProjectionToTerm<Goal> leftCoeff, ProjectionToTerm<Goal> rightCoeff) {
        return new PolynomialValuesCmpFeature(left, right, leftCoeff, rightCoeff, Cmp.DIVIDES);
    }

    @Override
    protected boolean filter(TacletApp app, PosInOccurrence pos,
            Goal goal, MutableState mState) {
        final TacletApp tacletApp = (TacletApp) app;
        return compare(getPolynomial(left, leftCoeff, tacletApp, pos, goal, mState),
            getPolynomial(right, rightCoeff, tacletApp, pos, goal, mState));
    }

    private boolean compare(Polynomial leftPoly, Polynomial rightPoly) {
        return switch (cmp) {
            case LT -> leftPoly.valueLess(rightPoly);
            case LEQ -> leftPoly.valueLeq(rightPoly);
            case EQ -> leftPoly.valueEq(rightPoly);
            case DIVIDES -> dividesCmp(leftPoly, rightPoly);
        };
    }

    private static boolean dividesCmp(Polynomial leftPoly, Polynomial rightPoly) {
        // we currently only support constant polynomials
        assert leftPoly.getParts().isEmpty();
        assert rightPoly.getParts().isEmpty();
        if (leftPoly.getConstantTerm().signum() == 0) {
            return true;
        }
        if (rightPoly.getConstantTerm().signum() == 0) {
            return false;
        }
        return leftPoly.getConstantTerm().mod(rightPoly.getConstantTerm().abs()).signum() == 0;
    }

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
