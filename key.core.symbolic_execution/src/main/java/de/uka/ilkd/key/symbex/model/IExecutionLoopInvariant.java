/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbex.model;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.symbex.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbex.model.impl.ExecutionLoopInvariant;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop invariant application.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopInvariant} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopInvariant
 */
public interface IExecutionLoopInvariant extends IExecutionNode<SourceElement> {
    /**
     * Returns the used {@link LoopSpecification}.
     *
     * @return The used {@link LoopSpecification}.
     */
    LoopSpecification getLoopInvariant();

    /**
     * Returns the loop statement which is simulated by its loop invariant.
     *
     * @return The loop statement which is simulated by its loop invariant.
     */
    While getLoopStatement();

    /**
     * Checks if the loop invariant is initially valid.
     *
     * @return {@code true} initially valid, {@code false} initially invalid.
     */
    boolean isInitiallyValid();
}
