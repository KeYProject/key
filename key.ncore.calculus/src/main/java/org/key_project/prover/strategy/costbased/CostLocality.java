/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased;

/**
 * Reuse-locality of a {@link CostClassifiable} strategy cost component: how much of the changing
 * proof state its cost may depend on. Ordered from most to least reusable.
 *
 * @see CostClassifiable#locality()
 */
public enum CostLocality {
    /** Cost is fixed by the rule application + match + find subterm; reusable indefinitely. */
    STABLE,
    /** Cost also reads the whole find formula; reusable only while that formula is unchanged. */
    WEAK_STABLE,
    /** Cost may depend on arbitrary changing proof state; never reusable. */
    VOLATILE
}
