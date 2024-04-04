/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionStart;

import org.key_project.util.collection.ImmutableList;

/**
 * <p>
 * The start node of a symbolic execution tree.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionStart} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionStart
 */
public interface IExecutionStart extends IExecutionNode<SourceElement> {
    /**
     * The default name of an {@link IExecutionStart}.
     */
    String DEFAULT_START_NODE_NAME =
        INTERNAL_NODE_NAME_START + "start" + INTERNAL_NODE_NAME_END;

    /**
     * Returns the up to now discovered {@link IExecutionTermination}s.
     *
     * @return The up to now discovered {@link IExecutionTermination}s.
     */
    ImmutableList<IExecutionTermination> getTerminations();
}
