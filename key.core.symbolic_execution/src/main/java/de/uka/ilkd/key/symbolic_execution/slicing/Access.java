/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.slicing;

import java.util.Objects;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.collection.ImmutableArray;

public class Access {
    /**
     * The {@link ProgramVariable} or {@code null} if an array index is accessed.
     */
    private final ProgramVariable programVariable;

    /**
     * The accessed array index or {@code null} if it is not an array access.
     */
    private final ImmutableArray<Term> dimensionExpressions;

    /**
     * Constructor.
     *
     * @param programVariable The accessed {@link ProgramVariable}.
     */
    public Access(ProgramVariable programVariable) {
        assert programVariable != null;
        this.programVariable = programVariable;
        this.dimensionExpressions = null;
    }

    /**
     * Constructor.
     *
     * @param dimensionExpressions The accessed array index.
     */
    public Access(ImmutableArray<Term> dimensionExpressions) {
        assert dimensionExpressions != null;
        this.programVariable = null;
        this.dimensionExpressions = dimensionExpressions;
    }

    /**
     * Constructor.
     *
     * @param dimensionExpressions The accessed array index.
     */
    public Access(Term... dimensionExpressions) {
        assert dimensionExpressions != null;
        this.programVariable = null;
        this.dimensionExpressions = new ImmutableArray<>(dimensionExpressions);
    }

    /**
     * Returns the {@link ProgramVariable} or {@code null} if an array index is accessed.
     *
     * @return The {@link ProgramVariable} or {@code null} if an array index is accessed.
     */
    public ProgramVariable getProgramVariable() {
        return programVariable;
    }

    /**
     * Returns the accessed array index or {@code null} if it is not an array access.
     *
     * @return The accessed array index or {@code null} if it is not an array access.
     */
    public ImmutableArray<Term> getDimensionExpressions() {
        return dimensionExpressions;
    }

    /**
     * Checks if an array index is accessed.
     *
     * @return {@code true} array index is accessed, {@code false} otherwise.
     */
    public boolean isArrayIndex() {
        return dimensionExpressions != null;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        int hashcode = 5;
        hashcode = hashcode * 17 + (programVariable != null ? programVariable.hashCode() : 0);
        hashcode =
            hashcode * 17 + (dimensionExpressions != null ? dimensionExpressions.hashCode() : 0);
        return hashcode;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(Object obj) {
        if (obj instanceof Access) {
            Access other = (Access) obj;
            return Objects.equals(programVariable, other.getProgramVariable())
                    && Objects.equals(dimensionExpressions, other.getDimensionExpressions());
        } else {
            return false;
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        if (programVariable != null) {
            return programVariable.toString();
        } else if (dimensionExpressions != null) {
            return dimensionExpressions.toString();
        } else {
            return "Undefined";
        }
    }
}
