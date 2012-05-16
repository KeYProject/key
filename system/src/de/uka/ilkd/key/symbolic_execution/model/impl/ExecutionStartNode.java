package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStartNode;

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
