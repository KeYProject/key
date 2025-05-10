/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbex.model;

import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.symbex.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbex.model.impl.ExecutionLoopStatement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop. e.g. {@code while(x >= 0)}. The
 * loop condition ({@code x >= 0}) itself is represented as {@link IExecutionLoopCondition}
 * instance.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopStatement} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopStatement
 */
public interface IExecutionLoopStatement extends IExecutionBlockStartNode<LoopStatement> {
}
