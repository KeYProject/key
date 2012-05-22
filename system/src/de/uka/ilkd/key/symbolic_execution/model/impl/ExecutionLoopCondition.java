package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * The default implementation of {@link IExecutionLoopCondition}.
 * @author Martin Hentschel
 */
public class ExecutionLoopCondition extends AbstractExecutionStateNode<LoopStatement> implements IExecutionLoopCondition {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionLoopCondition(Node proofNode) {
      super(proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getGuardExpression().toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Expression getGuardExpression() {
      return getActiveStatement().getGuardExpression();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PositionInfo getGuardExpressionPositionInfo() {
      return getGuardExpression().getPositionInfo();
   }
}
