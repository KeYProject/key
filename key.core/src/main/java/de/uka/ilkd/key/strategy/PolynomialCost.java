/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

/*
 * Theory-internal cost constants for the integer arithmetic strategy, grouped by the arithmetic
 * sub-theory they belong to (each holder is a top-level class of its own so it can move with its
 * sub-strategy when IntegerStrategy is split). Cross-theory levels stay in
 * {@link org.key_project.prover.strategy.costbased.CostBand}; only the arithmetic-internal ordering
 * lives here. All values are byte-identical to the literals they replace.
 */

/** Polynomial normal-form canonicalisation (Buchberger normalisation) — the "basic" substrate. */
final class PolynomialCost {
    private PolynomialCost() {}

    /** elimSubNeg, homo, pullOutFactor, elimOneLeft/Right. */
    static final long EXPAND = -120;
    static final long MUL_ORDER = -100;
    static final long MUL_ASSOC = -80;
    static final long ADD_ORDER = -60;
    static final long ADD_ASSOC = -10;
    /** polySimp_dist base; the distLeft sub-case is {@code DISTRIBUTE + 20}. */
    static final long DISTRIBUTE = -35;
    static final long PULLOUT_GCD = -2250;
}
