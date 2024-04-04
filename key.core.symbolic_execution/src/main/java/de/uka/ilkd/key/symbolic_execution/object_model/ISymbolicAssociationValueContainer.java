/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.AbstractSymbolicAssociationValueContainer;

import org.key_project.util.collection.ImmutableList;

/**
 * <p>
 * This interface is not instantiated directly because it defines only the common behavior of
 * {@link ISymbolicState} and {@link ISymbolicObject} which is to contain associations (references
 * to other {@link ISymbolicObject}s) and values (local variables of simple types).
 * </p>
 * <p>
 * The default abstract implementation is {@link AbstractSymbolicAssociationValueContainer}.
 * </p>
 *
 * @author Martin Hentschel
 * @see AbstractSymbolicAssociationValueContainer
 * @see ISymbolicObject
 * @see ISymbolicState
 */
public interface ISymbolicAssociationValueContainer extends ISymbolicElement {
    /**
     * Returns the contained associations.
     *
     * @return The contained associations.
     */
    ImmutableList<ISymbolicAssociation> getAssociations();

    /**
     * Returns the {@link ISymbolicAssociation} with the given {@link IProgramVariable}.
     *
     * @param programVariable The {@link IProgramVariable} for which the
     *        {@link ISymbolicAssociation} is requested.
     * @param isArrayIndex Is array index?
     * @param arrayIndex The array index.
     * @param condition The optional condition under which this association is valid.
     * @return The found {@link ISymbolicAssociation} or {@code null} if no
     *         {@link ISymbolicAssociation} is available with the given {@link IProgramVariable}.
     */
    ISymbolicAssociation getAssociation(IProgramVariable programVariable,
            boolean isArrayIndex, Term arrayIndex, Term condition);

    /**
     * Returns the contained values.
     *
     * @return The contained values.
     */
    ImmutableList<ISymbolicValue> getValues();

    /**
     * Returns the {@link ISymbolicValue} with the given {@link IProgramVariable}.
     *
     * @param programVariable The {@link IProgramVariable} for which the {@link ISymbolicValue} is
     *        requested.
     * @param isArrayIndex Is array index?
     * @param arrayIndex The array index.
     * @param condition The optional condition under which this value is valid.
     * @return The found {@link ISymbolicValue} or {@code null} if no {@link ISymbolicValue} is
     *         available with the given {@link IProgramVariable}.
     */
    ISymbolicValue getValue(IProgramVariable programVariable, boolean isArrayIndex,
            Term arrayIndex, Term condition);
}
