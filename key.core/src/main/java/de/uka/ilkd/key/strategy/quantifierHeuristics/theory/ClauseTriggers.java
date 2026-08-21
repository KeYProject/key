/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy.quantifierHeuristics.theory;

import java.util.ArrayList;
import java.util.List;

import de.uka.ilkd.key.logic.JTerm;

/**
 * What trigger selection found for one clause: the triggers of each literal, and whether
 * elements of several literals combined into a covering multi-trigger.
 *
 * A clause is covered if some literal has a covering trigger or a covering multi-trigger was
 * built. An uncovered clause is never instantiated through its own terms; it is the case
 * {@link TriggerSupport#fallbackTriggers} exists for.
 *
 * @param clause the clause as trigger selection read it
 * @param literals the triggers found per literal, in the order of {@code clause.literals()}
 * @param multiCovered whether a covering multi-trigger was built from the literals' elements
 */
public record ClauseTriggers(ClauseAnalysis clause, List<LiteralTriggers> literals,
        boolean multiCovered) {

    /** Whether some literal has a covering trigger or a covering multi-trigger was built. */
    public boolean covered() {
        if (multiCovered) {
            return true;
        }
        for (final LiteralTriggers literal : literals) {
            if (!literal.covering().isEmpty()) {
                return true;
            }
        }
        return false;
    }

    /** The literals that yielded neither a covering trigger nor an element. */
    public List<JTerm> literalsWithoutTrigger() {
        final List<JTerm> result = new ArrayList<>();
        for (final LiteralTriggers literal : literals) {
            if (literal.isEmpty()) {
                result.add(literal.literal());
            }
        }
        return result;
    }
}
