/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.termProjection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.metaconstruct.arith.Monomial;

import org.key_project.logic.Term;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;

/**
 * Projection for dividing one monomial by another.
 */
public class ReduceMonomialsProjection implements ProjectionToTerm<Goal> {

    private final ProjectionToTerm<Goal> dividend, divisor;

    private ReduceMonomialsProjection(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        this.dividend = dividend;
        this.divisor = divisor;
    }

    public static ProjectionToTerm<Goal> create(ProjectionToTerm<Goal> dividend,
            ProjectionToTerm<Goal> divisor) {
        return new ReduceMonomialsProjection(dividend, divisor);
    }

    @Override
    public Term toTerm(RuleApp app, PosInOccurrence pos, Goal goal, MutableState mState) {
        final Term dividendT = dividend.toTerm(app, pos, goal, mState);
        final Term divisorT = divisor.toTerm(app, pos, goal, mState);

        final Services services = goal.proof().getServices();
        final Monomial mDividend = Monomial.create(dividendT, services);
        final Monomial mDivisor = Monomial.create(divisorT, services);

        return mDivisor.reduce(mDividend).toTerm(services);
    }
}
