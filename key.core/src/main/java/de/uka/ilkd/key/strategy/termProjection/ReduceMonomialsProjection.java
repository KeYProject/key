/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

/**
 * Projection for dividing one monomial by another.
 */
public class ReduceMonomialsProjection implements ProjectionToTerm {

    private final ProjectionToTerm dividend, divisor;

    private ReduceMonomialsProjection(ProjectionToTerm dividend, ProjectionToTerm divisor) {
        this.dividend = dividend;
        this.divisor = divisor;
    }

    public static ProjectionToTerm create(ProjectionToTerm dividend, ProjectionToTerm divisor) {
        return new ReduceMonomialsProjection(dividend, divisor);
    }

    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal) {
        final Term dividendT = dividend.toTerm(app, pos, goal);
        final Term divisorT = divisor.toTerm(app, pos, goal);

        final Services services = goal.proof().getServices();
        final Monomial mDividend = Monomial.create(dividendT, services);
        final Monomial mDivisor = Monomial.create(divisorT, services);

        return mDivisor.reduce(mDividend).toTerm(services);
    }
}
