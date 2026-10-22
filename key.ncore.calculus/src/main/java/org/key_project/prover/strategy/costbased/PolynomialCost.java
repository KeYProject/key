/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.strategy.costbased;

/** Polynomial normal-form canonicalisation (Buchberger normalisation) — the "basic" substrate. */
final public class PolynomialCost {
    private PolynomialCost() {}

    /** elimSubNeg, homo, pullOutFactor, elimOneLeft/Right. */
    static public final long EXPAND = -120;
    static public final long MUL_ORDER = -100;
    static public final long MUL_ASSOC = -80;
    static public final long ADD_ORDER = -60;
    static public final long ADD_ASSOC = -10;
    /** polySimp_dist base; the distLeft sub-case is {@code DISTRIBUTE + 20}. */
    static public final long DISTRIBUTE = -35;
    static public final long PULLOUT_GCD = -2250;
}
