/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbex.model;

import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.symbex.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbex.model.impl.ExecutionBranchStatement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a node which creates multiple child
 * branches defined by branch conditions ({@link IExecutionBranchCondition}), e.g.
 * {@code if(x >= 0)}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionBranchStatement} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionBranchStatement
 */
public interface IExecutionBranchStatement extends IExecutionBlockStartNode<BranchStatement> {
}
