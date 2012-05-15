package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionBranchNode;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;

import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.proof.Node;

/**
 * The default implementation of {@link IExecutionBranchNode}.
 * @author Martin Hentschel
 */
public class ExecutionBranchNode extends AbstractExecutionStateNode<BranchStatement> implements IExecutionBranchNode {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionBranchNode(Node proofNode) {
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
