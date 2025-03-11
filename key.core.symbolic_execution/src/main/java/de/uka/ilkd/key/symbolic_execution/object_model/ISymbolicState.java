/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.symbolic_execution.object_model.impl.SymbolicState;

/**
 * <p>
 * Represents the symbolic state of an {@link ISymbolicLayout}.
 * </p>
 * <p>
 * The default implementation is {@link SymbolicState}.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicState
 */
public interface ISymbolicState extends ISymbolicAssociationValueContainer {
    /**
     * Returns the name of this state.
     *
     * @return The name of this state.
     */
    String getName();
}
