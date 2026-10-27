/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

/** Division / modulo and DefOps expansion ({@code polyDivision}, {@code defOps_*}). */
final class DivModCost {
    private DivModCost() {}

    static final long POLY_DIVISION = -2250;
    static final long EXPAND_MODULO = -600;
    /** extra cost for defOps_div/jdiv applied below a modality. */
    static final long BELOW_MODALITY = 200;
    static final long EXPAND_RANGES = -8000;
    static final long MOD_HOMO_EQ = -5000;
    static final long EXPAND_NUMERIC_OP = -500;
    /** defOps_jdiv_inline for a literal numerator (eager, concrete division). */
    static final long INLINE = -5000;
    /** literal-only division / modulo (defOps_mod, off-mode jdiv_inline). */
    static final long MOD = -4000;
    /** modulo expansion for a polynomial (non-literal) modulus (defOps_mod). */
    static final long MOD_EXPAND = -3500;
}
