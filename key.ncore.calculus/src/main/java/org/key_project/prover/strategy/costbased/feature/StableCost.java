/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * The stable end of the three-way locality scale ({@code StableCost} / {@link WeakStableCost} /
 * {@link VolatileCost}): marks a {@link Feature} whose cost for a given rule application does not
 * change as the proof goes on, asked to score the same application now or much later, it always
 * returns the same cost. Such a feature derives its cost only from the rule application it is
 * scoring, the taclet, how its schema variables and {@code \assumes} matched, and the term the
 * application is applied to, and from nothing else about the goal.
 *
 * <p>
 * In particular, the cost of a feature you mark here must NOT depend on any of the following, all
 * of
 * which keep changing while a proof is being built:
 * <ul>
 * <li>the other formulas in the sequent,</li>
 * <li>which rules have already been applied earlier in the proof,</li>
 * <li>which instantiations have already been tried on the goal,</li>
 * <li>or any other changing or global state.</li>
 * </ul>
 * (Your feature does not have to look at the applied-to term to qualify, one that scores an
 * application purely from how its schema variables were matched is fine too. The only thing that
 * matters is that nothing your feature reads can have a different value later on.)
 *
 * <p>
 * <b>Why this annotation exists.</b> To pick the next rule, the automatic strategy asks the
 * features
 * for the cost of every rule application it is currently considering and applies the cheapest. The
 * same applications come up for scoring over and over as the search proceeds, and recomputing their
 * costs each time is a large part of the strategy's running time. So when <em>all</em> the features
 * scoring an application return an unchanging cost, the prover computes that cost once and then
 * keeps
 * reusing it instead of recomputing. Reusing the old value is only correct if it really cannot have
 * changed, which is precisely the promise you make by adding this annotation. Add it only when you
 * are certain your feature's cost is fixed by the rule application alone.
 *
 * <p>
 * <b>Watch out for features that look fixed but are not.</b> A feature is volatile if it consults
 * anything the proof changes over time, for instance one that scans the other formulas of the
 * sequent, or ranks terms by when the proof first introduced their symbols: its answer, and hence
 * the cost, can differ from one moment to the next. Such a feature must be marked
 * {@link VolatileCost}, not this one. A feature that reads the whole find formula but nothing
 * further is in between, mark it {@link WeakStableCost}. When you are not sure, leave the feature
 * unmarked.
 *
 * <p>
 * <b>What if I get it wrong?</b> Leaving a feature unmarked is always safe: its cost is simply
 * recomputed every time and never reused, which only costs a little performance. Marking a feature
 * that is <em>not</em> in fact fixed, on the other hand, lets the strategy work with a stale cost
 * and can change, or even stall, the automatic search (it never makes a found proof invalid, but it
 * can
 * stop one from being found). To check your annotations, run the prover with
 * {@code -Dkey.strategy.costReuse.verify=true}: it recomputes every reused cost and prints a
 * warning whenever the reused value disagrees with a freshly computed one, pointing at the
 * offending
 * taclet.
 *
 * <p>
 * <b>Features built from other features.</b> If your feature combines sub-features, you may mark it
 * here only when every part it builds on, including helper objects such as term projections or term
 * generators, is itself fixed in this sense. The classifier verifies those parts automatically;
 * your annotation additionally vouches that the combining logic of your own feature reads nothing
 * that can change. Use {@link VolatileCost} to force a feature to be treated as not reusable.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface StableCost {
}
