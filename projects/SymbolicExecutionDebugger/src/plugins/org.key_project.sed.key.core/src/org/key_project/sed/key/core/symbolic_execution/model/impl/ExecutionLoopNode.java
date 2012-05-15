package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionLoopNode;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;

import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.proof.Node;

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
