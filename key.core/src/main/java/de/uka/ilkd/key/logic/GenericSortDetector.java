/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.Nullable;

/**
 * Detects occurrences of generic sorts within terms and sequents.
 * <p>
 * Generic sorts are schematic placeholders that may only appear in taclets; they must never occur
 * in a concrete sequent. This detector is meant to be used at <em>user-input/parser boundaries</em>
 * (problem sections, JML translation, interactive taclet instantiation) to reject such input early
 * with a clear message. It is deliberately <em>not</em> wired into term construction or automatic
 * proof search, where a generic-sort leak would be an implementation error to be found by other
 * means.
 * <p>
 * A sort is reported when {@link Sort#containsGenericSort()} holds. This catches a generic sort
 * even
 * when it is nested inside a parametric sort (e.g. {@code List<[E]>}, or the result sort of
 * {@code select<[E]>(...)}), not only when a term's own sort is itself a generic sort.
 *
 * @author KeY developers
 */
public final class GenericSortDetector {

    private GenericSortDetector() {}

    /**
     * @param term a term, may be {@code null}
     * @return the distinct sorts occurring in {@code term} (in a subterm's sort or a bound
     *         variable's sort) that are or contain a generic sort, in order of first occurrence;
     *         empty if none occurs
     */
    public static List<Sort> findIn(@Nullable JTerm term) {
        Set<Sort> found = new LinkedHashSet<>();
        collect(term, found);
        return new ArrayList<>(found);
    }

    /**
     * @param sequent a sequent, may be {@code null}
     * @return the distinct sorts occurring in any formula of {@code sequent} that are or contain a
     *         generic sort, in order of first occurrence; empty if none occurs
     */
    public static List<Sort> findIn(@Nullable Sequent sequent) {
        Set<Sort> found = new LinkedHashSet<>();
        if (sequent != null) {
            for (SequentFormula sf : sequent) {
                collect((JTerm) sf.formula(), found);
            }
        }
        return new ArrayList<>(found);
    }

    private static void collect(@Nullable JTerm term, Set<Sort> found) {
        if (term == null) {
            return;
        }
        if (term.sort().containsGenericSort()) {
            found.add(term.sort());
        }
        for (QuantifiableVariable qv : term.boundVars()) {
            if (qv.sort().containsGenericSort()) {
                found.add(qv.sort());
            }
        }
        for (int i = 0; i < term.arity(); i++) {
            collect(term.sub(i), found);
        }
    }
}
