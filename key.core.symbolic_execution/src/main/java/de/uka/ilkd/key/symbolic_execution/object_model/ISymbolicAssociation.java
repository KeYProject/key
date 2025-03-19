/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicAssociation;

/**
 * <p>
 * Represents an association of an {@link ISymbolicState} or {@link ISymbolicObject} which is a
 * reference to an {@link ISymbolicObject}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicAssociation}.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicAssociation
 */
public interface ISymbolicAssociation extends ISymbolicElement {
    /**
     * Returns a human readable name.
     *
     * @return A human readable name.
     */
    String getName();

    /**
     * Checks if an array index or a program variable is represented.
     *
     * @return {@code true} array index, {@code false} program variable.
     */
    boolean isArrayIndex();

    /**
     * Returns the represented array index or {@code null} if a program variable is represented..
     *
     * @return The represented array index or {@code null} if a program variable is represented..
     */
    Term getArrayIndex();

    /**
     * Returns the human readable array index or {@code null} if a program variable is represented..
     *
     * @return The human readable array index or {@code null} if a program variable is represented..
     */
    String getArrayIndexString();

    /**
     * Returns the represented {@link IProgramVariable}.
     *
     * @return The represented {@link IProgramVariable}.
     */
    IProgramVariable getProgramVariable();

    /**
     * Returns the represented {@link IProgramVariable} as human readable {@link String}.
     *
     * @return The represented {@link IProgramVariable} as human readable {@link String}.
     */
    String getProgramVariableString();

    /**
     * Returns the target {@link ISymbolicObject}.
     *
     * @return The target {@link ISymbolicObject}.
     */
    ISymbolicObject getTarget();

    /**
     * <p>
     * Returns the optional condition under which this association is valid.
     * </p>
     * <p>
     * The condition should be {@code null} by default. Only in rare cases, e.g. path condition is
     * not strong enough to describe the path completely, is a condition is provided.
     * </p>
     *
     * @return The optional condition under which this association is valid.
     */
    Term getCondition();

    /**
     * <p>
     * Returns the optional condition under which this association is valid as human readable
     * {@link String}.
     * </p>
     * <p>
     * The condition should be {@code null} by default. Only in rare cases, e.g. path condition is
     * not strong enough to describe the path completely, is a condition is provided.
     * </p>
     *
     * @return The optional condition under which this association is valid as human readable
     *         {@link String}.
     */
    String getConditionString();
}
