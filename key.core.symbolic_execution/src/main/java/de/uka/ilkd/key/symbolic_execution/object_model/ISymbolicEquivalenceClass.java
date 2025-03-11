/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.Term;

import org.key_project.util.collection.ImmutableList;

/**
 * An equivalence class which defines which {@link Term}s represent the same {@link ISymbolicObject}
 * in an {@link ISymbolicLayout}.
 *
 * @author Martin Hentschel
 */
public interface ISymbolicEquivalenceClass extends ISymbolicElement {
    /**
     * Returns the terms which represents the same {@link ISymbolicObject}.
     *
     * @return The terms which represents the same {@link ISymbolicObject}.
     */
    ImmutableList<Term> getTerms();

    /**
     * Checks if a {@link Term} is contained.
     *
     * @param term The {@link Term} to check.
     * @return {@code true} {@link Term} is contained, {@code false} {@link Term} is not contained.
     */
    boolean containsTerm(Term term);

    /**
     * Returns the terms which represents the same {@link ISymbolicObject} as human readable
     * {@link String}.
     *
     * @return The terms which represents the same {@link ISymbolicObject} as human readable
     *         {@link String}.
     */
    ImmutableList<String> getTermStrings();

    /**
     * Returns the most representative term.
     *
     * @return The most representative term.
     */
    Term getRepresentative();

    /**
     * Returns the most representative term as human readable {@link String}.
     *
     * @return The most representative term as human readable {@link String}.
     */
    String getRepresentativeString();
}
