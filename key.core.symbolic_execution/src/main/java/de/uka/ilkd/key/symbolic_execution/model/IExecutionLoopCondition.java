/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.statement.JavaStatement;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.impl.ExecutionLoopCondition;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop condition, e.g. {@code x >= 0}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopCondition} which is instantiated via a
 * {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 *
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopCondition
 */
public interface IExecutionLoopCondition extends IExecutionBlockStartNode<JavaStatement> {
    /**
     * Returns the loop expression which is executed.
     *
     * @return The executed loop expression.
     */
    Expression getGuardExpression();

    /**
     * Returns the code position of the executed loop expression ({@link #getGuardExpression()}).
     *
     * @return The code of the executed loop expression.
     */
    PositionInfo getGuardExpressionPositionInfo();
}
