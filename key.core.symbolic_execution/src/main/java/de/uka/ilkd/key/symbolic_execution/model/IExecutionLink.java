/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

/**
 * A link between two {@link IExecutionNode}s.
 *
 * @author Martin Hentschel
 */
public interface IExecutionLink {
    /**
     * Returns the source.
     *
     * @return The source.
     */
    IExecutionNode<?> getSource();

    /**
     * Returns the target.
     *
     * @return The target.
     */
    IExecutionNode<?> getTarget();
}
