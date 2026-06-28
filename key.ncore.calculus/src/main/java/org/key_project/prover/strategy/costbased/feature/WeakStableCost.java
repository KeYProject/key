/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The middle of the three-way locality scale ({@link StableCost} / {@code WeakStableCost} /
 * {@link VolatileCost}): marks a {@link Feature} that is stable only as long as the formula the
 * application sits in is unchanged. Unlike {@link StableCost}, which looks only at the applied-to
 * term (and below) -- which a surviving application keeps fixed -- a feature marked here reads the
 * whole find formula, so its cost can change when a sibling part of that formula is rewritten even
 * though the applied-to term is untouched. Its cost may therefore be reused only while the find
 * formula is still the one present when the cost was first computed; the strategy checks this and
 * recomputes as soon as the formula is rewritten.
 *
 * <p>
 * It must still read nothing beyond the find formula: not the other formulas of the sequent, the
 * rules already applied, the instantiations already tried, nor any other goal state -- a feature
 * that does is {@link VolatileCost}. Everything {@link StableCost} says otherwise applies here too
 * (unmarked is always safe; how a combining feature and its term-generators are handled; the
 * {@code -Dkey.strategy.costReuse.verify=true} cross-check) -- read "the find formula" for "the
 * applied-to term".
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface WeakStableCost {
}
