package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionBranchCondition;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * The default implementation of {@link IExecutionBranchCondition}.
 * @author Martin Hentschel
 */
public class ExecutionBranchCondition extends AbstractExecutionNode implements IExecutionBranchCondition {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionBranchCondition(Node proofNode) {
      super(proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getProofNodeInfo().getBranchLabel();
   }
}
