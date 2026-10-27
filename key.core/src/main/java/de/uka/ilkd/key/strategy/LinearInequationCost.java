/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy;

/** Linear inequation solving — the Omega / Fourier-Motzkin machinery ({@code inEqSimp_*}). */
final class LinearInequationCost {
    private LinearInequationCost() {}

    static final long PROPAGATION = -2400;
    static final long SATURATE = -1900;
    /** General GCD normalisation of inequations — confluent, hence safe to apply eagerly. */
    static final long PULLOUT_GCD_CONFLUENT = -2150;
    static final long FOR_NORMALISATION = -1100;
    static final long MOVE_LEFT = -90;
    static final long MAKE_NON_STRICT = -80;
    static final long CONTRAD = -60;
    static final long COMMUTE = -40;
    static final long STRENGTHEN = -30;
    static final long ANTISYMM = -20;
    /**
     * Faster antecedent-specialised GCD pull-out, but <em>not</em> confluent (the result can depend
     * on application order), hence pinned near baseline so it fires only opportunistically — in
     * contrast to the eager {@link #PULLOUT_GCD_CONFLUENT}.
     */
    static final long PULLOUT_GCD_ANTEC_NONCONFLUENT = -10;
}
