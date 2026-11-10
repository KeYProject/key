/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/// Polynomial _equation solving_ (Gaussian / Gröbner). These `polySimp_*` rule sets
/// live
/// here rather than in [PolynomialCost] on purpose: they do not just canonicalize a term, they
/// _derive_ from and apply equations, so they belong to the "linear" (solving) layer next to
/// [LinearInequationCost].
final public class LinearEquationCost {
    private LinearEquationCost() {}

    // The base costs of apply_equations / apply_equations_andOr are combination-shared with
    // FOLStrategy (conflict-dispatched; the Integer halves use the monomial ordering as
    // demodulation guard): see CombinationCost.ORDERED_REWRITING and
    // CombinationCost.CNF_CONVERSION.

    /** polySimp_balance, polySimp_normalise. */
    static public final long BALANCE = -30;
    /// polySimp\_applyEq — a small tie-break rider on top of the general demodulation cost
    /// [CombinationCost#ORDERED_REWRITING] (the `apply_eq_monomials` taclet carries both
    /// rule sets, so the effective cost is their sum). The rigid variant polySimp\_applyEqRigid is
    /// written `APPLY_EQ_MONOMIAL_TIEBREAK + 1` at the call site; that +1 is only an
    /// (uninteresting) tie-break between the two rules, a step-3 candidate to flatten. Step-3 idea:
    /// test whether this specialised variant is needed at all, or should just be a small delta
    /// preferring the original `apply_equations` rules.
    static public final long APPLY_EQ_MONOMIAL_TIEBREAK = 1;
}
