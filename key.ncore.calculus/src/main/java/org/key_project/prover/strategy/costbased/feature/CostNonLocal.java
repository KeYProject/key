/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased.feature;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Explicitly marks a {@link Feature} as NON-local for strategy-cost reuse (see
 * {@code de.uka.ilkd.key.strategy.CostReuse}): its cost may depend on goal-global state (other
 * sequent formulas, applied rules, instantiation context, ...), so it must be recomputed on every
 * re-expansion.
 *
 * <p>
 * This is an override: it wins over the automatic classification. Use it on a composite feature
 * that would otherwise be auto-classified local (because all its children are local) but that
 * itself reads goal-global state, or to defensively pin a feature whose locality is in doubt. The
 * default for an unannotated leaf feature is already non-local, so this annotation is only needed
 * to
 * override the automatic decision.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target(ElementType.TYPE)
public @interface CostNonLocal {
}
