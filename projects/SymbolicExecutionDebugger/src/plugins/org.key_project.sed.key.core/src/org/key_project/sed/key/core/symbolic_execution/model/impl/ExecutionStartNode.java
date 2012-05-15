package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionStartNode;

import de.uka.ilkd.key.proof.Node;

/**
 * The default implementation of {@link IExecutionStartNode}.
 * @author Martin Hentschel
 */
public class ExecutionStartNode extends AbstractExecutionNode implements IExecutionStartNode {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionStartNode(Node proofNode) {
      super(proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return DEFAULT_START_NODE_NAME;
   }
}
