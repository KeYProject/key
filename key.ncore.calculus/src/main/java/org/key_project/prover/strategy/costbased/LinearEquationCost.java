/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/**
 * Polynomial <em>equation solving</em> (Gaussian / Gröbner). These {@code polySimp_*} rule sets
 * live
 * here rather than in {@link PolynomialCost} on purpose: they do not just canonicalise a term, they
 * <em>derive</em> from and apply equations, so they belong to the "linear" (solving) layer next to
 * {@link LinearInequationCost}.
 */
final public class LinearEquationCost {
    private LinearEquationCost() {}

    // The base costs of apply_equations / apply_equations_andOr are combination-shared with
    // FOLStrategy (conflict-dispatched; the Integer halves use the monomial ordering as
    // demodulation guard): see CombinationCost.ORDERED_REWRITING and
    // CombinationCost.CNF_CONVERSION.

    /** polySimp_balance, polySimp_normalise. */
    static public final long BALANCE = -30;
    /**
     * polySimp_applyEq — a small tie-break rider on top of the general demodulation cost
     * {@link CombinationCost#ORDERED_REWRITING} (the {@code apply_eq_monomials} taclet carries both
     * rule sets, so the effective cost is their sum). The rigid variant polySimp_applyEqRigid is
     * written {@code APPLY_EQ_MONOMIAL_TIEBREAK + 1} at the call site; that +1 is only an
     * (uninteresting) tie-break between the two rules, a step-3 candidate to flatten. Step-3 idea:
     * test whether this specialised variant is needed at all, or should just be a small delta
     * preferring the original {@code apply_equations} rules.
     */
    static public final long APPLY_EQ_MONOMIAL_TIEBREAK = 1;
}
