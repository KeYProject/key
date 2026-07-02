/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The volatile end of the three-way locality scale ({@link StableCost} / {@link WeakStableCost} /
 * {@code VolatileCost}): marks a {@link Feature} whose cost for a rule application can come out
 * differently as the proof goes on, because it reads goal state that keeps changing -- the other
 * formulas in the sequent, which rules have already been applied, which instantiations have been
 * tried, and so on. The automatic strategy must ask it for a fresh cost every time and may never
 * reuse an earlier value (see {@link StableCost} for what that reuse is and why it must be sound).
 *
 * <p>
 * An unmarked feature is already recomputed every time, so on an ordinary feature this annotation
 * changes no behaviour; it is documentation. You need it in two cases:
 * <ul>
 * <li>on a feature that <em>combines</em> sub-features which are each individually fixed, yet whose
 * own combining logic reads changing goal state -- without the annotation the classifier would
 * wrongly conclude the whole combination is fixed; and</li>
 * <li>on a feature that <em>looks</em> fixed but is not, to pin it down (ideally with a short
 * comment) so nobody later mistakenly marks it {@link StableCost} -- for example one that scans the
 * other formulas of the sequent, whose result changes as those formulas come and go.</li>
 * </ul>
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface VolatileCost {
}
