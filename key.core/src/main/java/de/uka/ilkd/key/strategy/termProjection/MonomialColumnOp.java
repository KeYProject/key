/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import java.math.BigInteger;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.LexPathOrdering;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

import org.key_project.logic.Term;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

public class MonomialColumnOp extends AbstractDividePolynomialsProjection {

    private MonomialColumnOp(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        super(leftCoefficient, polynomial);
    }

    public static ProjectionToTerm<Goal> create(ProjectionToTerm<Goal> leftCoefficient,
            ProjectionToTerm<Goal> polynomial) {
        return new MonomialColumnOp(leftCoefficient, polynomial);
    }

    @Override
    protected Term divide(Monomial numerator, BigInteger denominator, Services services) {
        final BigInteger newRightCoeff =
            LexPathOrdering.divide(numerator.getCoefficient(), denominator);
        return numerator.setCoefficient(newRightCoeff).toTerm(services);
    }
}
