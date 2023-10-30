/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicObject;

/**
 * <p>
 * Represents a symbolic object in an {@link ISymbolicLayout}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicObject}.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicObject
 */
public interface ISymbolicObject extends ISymbolicAssociationValueContainer {
    /**
     * Returns the name of this object.
     *
     * @return The name of this object.
     */
    Term getName();

    /**
     * Returns the name of this object as human readable {@link String}.
     *
     * @return The name of this object as human readable {@link String}.
     */
    String getNameString();

    /**
     * Returns the type of this object.
     *
     * @return The type of this object.
     */
    Sort getType();

    /**
     * Returns the type of this object as human readable string.
     *
     * @return The type of this object as human readable string.
     */
    String getTypeString();
}
