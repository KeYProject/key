/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/*
 * Theory-internal cost constants for the integer arithmetic strategy, grouped by the arithmetic
 * sub-theory they belong to. The grouping deliberately anticipates a future split of
 * IntegerStrategy into separate sub-strategies (polynomial / linear / non-linear / div-mod): each
 * holder is meant to move with its sub-strategy. Cross-theory levels stay in
 * {@link org.key_project.prover.strategy.costbased.CostBand}; only the arithmetic-internal ordering
 * lives here. All values are byte-identical to the literals they replace.
 *
 * The file is named after the integer-arithmetic *theory*; a plain "IntegerCost(s)" would suggest
 * an integer-valued cost type (an implementation of RuleAppCost) rather than a holder of cost
 * constants.
 */


/** Division / modulo and DefOps expansion ({@code polyDivision}, {@code defOps_*}). */
final public class DivModCost {
    private DivModCost() {}

    static public final long POLY_DIVISION = -2250;
    static public final long EXPAND_MODULO = -600;
    /** extra cost for defOps_div/jdiv applied below a modality. */
    static public final long BELOW_MODALITY = 200;
    static public final long EXPAND_RANGES = -8000;
    static public final long MOD_HOMO_EQ = -5000;
    static public final long EXPAND_NUMERIC_OP = -500;
    /** defOps_jdiv_inline for a literal numerator (eager, concrete division). */
    static public final long INLINE = -5000;
    /** literal-only division / modulo (defOps_mod, off-mode jdiv_inline). */
    static public final long MOD = -4000;
    /** modulo expansion for a polynomial (non-literal) modulus (defOps_mod). */
    static public final long MOD_EXPAND = -3500;
}
