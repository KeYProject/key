/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

/** Non-linear arithmetic — cross-multiplication, sign cases, root inferences (Model Search). */
final class NonlinearArithmeticCost {
    private NonlinearArithmeticCost() {}

    /**
     * inEqSimp_nonLin (cross-multiplication) base; case-distinction offsets are
     * {@code MULTIPLY + n}.
     */
    static final long MULTIPLY = 1000;
    /**
     * Divide an inequation by a factor of known sign/bound to bound the quotient (the
     * {@code divide_inEq*} taclets) — the inverse of cross-multiplication. Kept clearly more eager
     * than {@link #MULTIPLY}, since dividing/reducing is safer and more productive than
     * multiplying.
     */
    static final long DIVIDE_INEQUATION = -1400;
    static final long SPLIT_EQ = -100;
}
