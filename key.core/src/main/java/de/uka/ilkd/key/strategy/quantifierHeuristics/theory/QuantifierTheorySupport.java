/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

/**
 * A theory that contributes to quantifier instantiation on both counts: it selects which of its
 * subterms make a trigger, and it answers the questions the heuristic asks about terms.
 *
 * The two halves are separate interfaces because they travel differently. A front end registers
 * the theories of its own terms through {@link QuantifierTheorySupports}; one without a heap
 * implements {@link TheoryReasoning} alone.
 */
public interface QuantifierTheorySupport extends TriggerSupport, TheoryReasoning {
}
