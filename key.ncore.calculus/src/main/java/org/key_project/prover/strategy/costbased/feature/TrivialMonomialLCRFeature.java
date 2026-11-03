/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased.feature;

import java.util.function.BiFunction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.Term;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.ITacletApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.feature.helper.arith.Monomial;
import org.key_project.prover.strategy.costbased.termProjection.ProjectionToTerm;


/**
 * Return zero of the least common reducible of two monomials is so trivial that it is not necessary
 * to do the critical pair completion
 * <p>
 * "A critical-pair/completion algorithm for finitely generated ideals in rings"
 */
@StableCost
public class TrivialMonomialLCRFeature<GOAL extends ProofGoal<GOAL>>
        extends BinaryTacletAppFeature<GOAL> {
    private final ProjectionToTerm<GOAL> a, b;
    // creates a monomial from a given term
    private final BiFunction<Term, LogicServices, Monomial> builder;

    private TrivialMonomialLCRFeature(ProjectionToTerm<GOAL> a, ProjectionToTerm<GOAL> b,
            BiFunction<Term, LogicServices, Monomial> builder) {
        this.a = a;
        this.b = b;
        this.builder = builder;
    }

    public static <GOAL extends ProofGoal<GOAL>> Feature create(ProjectionToTerm<GOAL> a,
            ProjectionToTerm<GOAL> b,
            BiFunction<Term, LogicServices, Monomial> builder) {
        return new TrivialMonomialLCRFeature(a, b, builder);
    }

    @Override
    protected boolean filter(ITacletApp app, PosInOccurrence pos, GOAL goal, MutableState mState) {
        final LogicServices services = goal.proof().getServices();
        final Monomial aMon = builder.apply(a.toTerm(app, pos, goal, mState), services);
        final Monomial bMon = builder.apply(b.toTerm(app, pos, goal, mState), services);

        /*
         * final BigInteger ac = aMon.getCoefficient (); final BigInteger bc = bMon.getCoefficient
         * ();
         *
         * if ( ac.mod ( bc ).signum () != 0 && bc.mod ( ac ).signum () != 0 ) return false;
         */

        return aMon.variablesAreCoprime(bMon);
    }
}
