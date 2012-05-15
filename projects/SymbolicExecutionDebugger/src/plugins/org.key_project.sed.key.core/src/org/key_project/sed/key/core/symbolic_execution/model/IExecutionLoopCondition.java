package org.key_project.sed.key.core.symbolic_execution.model;

import org.key_project.sed.key.core.symbolic_execution.SymbolicExecutionTreeBuilder;
import org.key_project.sed.key.core.symbolic_execution.model.impl.ExecutionLoopCondition;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.statement.LoopStatement;

/**
 * <p>
 * A node in the symbolic execution tree which represents a loop condition,
 * e.g. {@code x >= 0}.
 * </p>
 * <p>
 * The default implementation is {@link ExecutionLoopCondition} which
 * is instantiated via a {@link SymbolicExecutionTreeBuilder} instance.
 * </p>
 * @author Martin Hentschel
 * @see SymbolicExecutionTreeBuilder
 * @see ExecutionLoopCondition
 */
public interface IExecutionLoopCondition extends IExecutionStateNode<LoopStatement> {
   /**
    * Returns the loop expression which is executed.
    * @return The executed loop expression.
    */
   public Expression getGuardExpression();

   /**
    * Returns the code position of the executed loop expression ({@link #getGuardExpression()}).
    * @return The code of the executed loop expression.
    */
   public PositionInfo getGuardExpressionPositionInfo();
}
