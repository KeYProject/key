/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marks a {@link Feature} that is only <em>weakly</em> stable: its cost for a given rule
 * application
 * stays the same as long as the formula the application sits in is unchanged, but it may read that
 * whole formula, not just the term the application is applied to, so its cost can change if some
 * other part of the same formula (for instance above or beside the find position) is rewritten.
 *
 * <p>
 * This is the middle ground between {@link StableCost} and {@link VolatileCost}:
 * <ul>
 * <li>{@link StableCost}, fully stable: the cost looks only at the applied-to term (and below),
 * which a surviving application keeps unchanged, so the cost can always be reused.</li>
 * <li>{@link WeakStableCost}, weakly stable: the cost also reads the surrounding formula, so it
 * may be reused only while that find formula is still the very one that was present when the cost
 * was first computed; the strategy checks this and recomputes as soon as the formula is
 * rewritten.</li>
 * <li>{@link VolatileCost}, not stable: the cost depends on the wider goal and is never
 * reused.</li>
 * </ul>
 *
 * <p>
 * The cost of a feature you mark here must still NOT depend on anything the proof changes beyond
 * the
 * find formula:
 * <ul>
 * <li>the <em>other</em> formulas in the sequent,</li>
 * <li>which rules have already been applied earlier in the proof,</li>
 * <li>which instantiations have already been tried on the goal,</li>
 * <li>or any other changing or global state.</li>
 * </ul>
 * If your feature reads any of those, mark it {@link VolatileCost} instead, not this one. The only
 * extra freedom this annotation grants over {@link StableCost} is reading the find formula as a
 * whole.
 *
 * <p>
 * <b>What if I get it wrong?</b> As with {@link StableCost}, leaving a feature unmarked is always
 * safe (its cost is simply recomputed and never reused). Marking a feature here that actually
 * depends on the wider goal lets the strategy work with a stale cost; it never makes a found proof
 * invalid, but it can change or stall the search. Run {@code -Dkey.strategy.costReuse.verify=true}
 * to have every reused cost recomputed and checked against a fresh value.
 *
 * <p>
 * <b>Features built from other features.</b> As with {@link StableCost}, you may mark a combining
 * feature here only when every part it builds on is itself at most weakly stable; the classifier
 * verifies those parts automatically and your annotation vouches that your own combining logic
 * reads
 * nothing beyond the find formula.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface WeakStableCost {
}
