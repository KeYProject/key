/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.logic.sort.GenericSort;

import org.key_project.logic.op.QuantifiableVariable;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.Nullable;

/**
 * Detects occurrences of {@link GenericSort}s within terms and sequents.
 * <p>
 * Generic sorts are schematic placeholders that may only appear in taclets; they must never occur
 * in a concrete sequent. This detector is meant to be used at <em>user-input/parser boundaries</em>
 * (problem sections, JML translation, interactive taclet instantiation) to reject such input early
 * with a clear message. It is deliberately <em>not</em> wired into term construction or automatic
 * proof search, where a generic-sort leak would be an implementation error to be found by other
 * means.
 *
 * @author KeY developers
 */
public final class GenericSortDetector {

    private GenericSortDetector() {}

    /**
     * @param term a term, may be {@code null}
     * @return the first {@link GenericSort} occurring in {@code term} (in a subterm's sort or a
     *         bound variable's sort), or {@code null} if none occurs
     */
    public static @Nullable GenericSort findIn(@Nullable JTerm term) {
        if (term == null) {
            return null;
        }
        if (term.sort() instanceof GenericSort gs) {
            return gs;
        }
        for (QuantifiableVariable qv : term.boundVars()) {
            if (qv.sort() instanceof GenericSort gs) {
                return gs;
            }
        }
        for (int i = 0; i < term.arity(); i++) {
            GenericSort found = findIn(term.sub(i));
            if (found != null) {
                return found;
            }
        }
        return null;
    }

    /**
     * @param sequent a sequent, may be {@code null}
     * @return the first {@link GenericSort} occurring in any formula of {@code sequent}, or
     *         {@code null} if none occurs
     */
    public static @Nullable GenericSort findIn(@Nullable Sequent sequent) {
        if (sequent == null) {
            return null;
        }
        for (SequentFormula sf : sequent) {
            GenericSort found = findIn((JTerm) sf.formula());
            if (found != null) {
                return found;
            }
        }
        return null;
    }
}
