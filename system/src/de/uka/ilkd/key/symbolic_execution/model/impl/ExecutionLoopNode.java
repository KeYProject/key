package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionLoopNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * The default implementation of {@link IExecutionLoopNode}.
 * @author Martin Hentschel
 */
public class ExecutionLoopNode extends AbstractExecutionStateNode<LoopStatement> implements IExecutionLoopNode {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionLoopNode(Node proofNode) {
      super(proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getActiveStatement().toString();
   }
}
