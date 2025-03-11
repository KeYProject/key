/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.SourceElement;

import org.key_project.util.collection.ImmutableList;

/**
 * An extended {@link IExecutionNode} which groups several child nodes.
 *
 * @author Martin Hentschel
 */
public interface IExecutionBlockStartNode<S extends SourceElement> extends IExecutionNode<S> {
    /**
     * Checks if a block might be opened.
     *
     * @return {@code false} block is definitively not opened, {@code true} block is or might be
     *         opened.
     */
    boolean isBlockOpened();

    /**
     * Returns the up to now discovered {@link IExecutionNode}s.
     *
     * @return The up to now discovered {@link IExecutionNode}s.
     */
    ImmutableList<IExecutionNode<?>> getBlockCompletions();
}
