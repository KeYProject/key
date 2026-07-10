/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/**
 * Costs of the pull-out-select heap simplification pipeline, used by {@link JavaCardDLStrategy}.
 * This is the coherent heap/select cluster that is a candidate to be promoted into its own
 * component strategy later; it is kept in a dedicated holder to pre-stage that split.
 *
 * <p>
 * <b>Combination-relevant, not purely local:</b> this ladder is tuned <em>relative to</em> the
 * FOL/Integer {@code apply_equations} cost. In particular {@link #APPLY_SELECT_EQ} is chosen so
 * that, together with the cost of {@code apply_equations}, the effective cost of replacing a select
 * comes out at about −5700 (see the inline comment at {@code apply_select_eq}). Keep that coupling
 * in mind when changing either side.
 * </p>
 *
 * <p>
 * Values are byte-identical to the literals they replace; verify changes with a full runAllProofs
 * (as for {@link org.key_project.prover.strategy.costbased.CostBand}).
 * </p>
 */
final class HeapSelectCost {
    private HeapSelectCost() {}

    /** {@code pull_out_select} when the focus select sits below an update (pull it out harder). */
    static final long PULL_OUT_SELECT_BELOW_UPDATE = -4200;

    /** {@code pull_out_select} otherwise. */
    static final long PULL_OUT_SELECT = -1900;

    /**
     * {@code apply_select_eq}: replace a not-yet-simplified select by the skolem constant of its
     * pull-out. Tuned so that with {@code apply_equations} the effective cost is about −5700.
     */
    static final long APPLY_SELECT_EQ = -1700;

    /** {@code simplify_select}: simplify the select term in the pulled-out equation. */
    static final long SIMPLIFY_SELECT = -5600;

    /** {@code apply_auxiliary_eq}: replace the skolem constant by its computed value. */
    static final long APPLY_AUXILIARY_EQ = -5500;

    /** {@code hide_auxiliary_eq}: hide the auxiliary equation once the constant is replaced. */
    static final long HIDE_AUXILIARY_EQ = -5400;

    /** {@code hide_auxiliary_eq_const}: same, for the constant-valued case. */
    static final long HIDE_AUXILIARY_EQ_CONST = -500;
}
