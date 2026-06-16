/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Marks a {@link Feature} whose cost is a pure function of the rule application and the subterm at
 * its find position -- i.e. it does NOT depend on other formulas of the sequent, the set of applied
 * rules on the branch, or any other goal-global state.
 *
 * <p>
 * This lets the strategy-cost reuse (see {@code de.uka.ilkd.key.strategy.CostReuse}) carry a
 * container's cost forward across the per-round re-expansion instead of recomputing it, as long as
 * the find position is unmodified. The default (no annotation) is the SAFE one: an unannotated leaf
 * feature is treated as non-local, so cost reuse simply does not apply to taclets that use it (they
 * are re-costed in full). Forgetting to annotate a new feature therefore costs performance, never
 * soundness.
 *
 * <p>
 * For a composite feature (one that combines child features) this annotation means "transparent":
 * the classifier recurses into the child features, so the composite counts as local only when all
 * of them are. There is no automatic structural transparency -- a composite is trusted only because
 * its author annotated it after checking that its own computation (including any non-Feature inputs
 * such as projections or term-generators) is find-local. Use {@link CostNonLocal} to force a
 * feature
 * to be treated as non-local.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface CostLocal {
}
