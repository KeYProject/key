package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionStatement;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;

/**
 * The default implementation of {@link IExecutionStatement}.
 * @author Martin Hentschel
 */
public class ExecutionStatement extends AbstractExecutionStateNode<SourceElement> implements IExecutionStatement {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionStatement(Node proofNode) {
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
