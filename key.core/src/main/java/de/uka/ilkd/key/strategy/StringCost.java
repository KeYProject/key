/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

/**
 * String/sequence-theory-internal ordering costs, used by {@link StringStrategy}.
 *
 * <p>
 * The theory splits into an <em>eager</em> side (negative costs: normalisations done early, named
 * here) and a <em>lazy unfold ladder</em> (positive costs: unfolding of string definitions is
 * deferred so it happens only when needed). The ladder is anchored to
 * {@code CostBand.DEFER.at(delta)} at the call sites, so each rule reads as "defer, by this much".
 * </p>
 *
 * <p>
 * Values are byte-identical to the literals they replace; changing one reorders string reasoning
 * (verify with a full runAllProofs, as for
 * {@link org.key_project.prover.strategy.costbased.CostBand}).
 * </p>
 */
final class StringCost {
    private StringCost() {}

    /** Translate an integer to its string representation ({@code integerToString}): very eager. */
    static final long INTEGER_TO_STRING = -10000;

    /**
     * Inline a {@code replace} when string, search- and replace-char are all literals
     * ({@code defOpsReplaceInline}): eager, closed-form.
     */
    static final long REPLACE_INLINE = -2500;

    /** Convert a char literal to an int literal (outside string functions). */
    static final long CHAR_TO_INT_LITERAL = -100;

    /**
     * Extra penalty for unfolding a string definition below a modal operator: postpone it until
     * the program has been symbolically executed. Shared by the {@code defOps*} rules.
     */
    static final long BELOW_MODALITY_PENALTY = 500;
}
