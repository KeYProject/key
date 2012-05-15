package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionMethodCall;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;

import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;

/**
 * The default implementation of {@link IExecutionMethodCall}.
 * @author Martin Hentschel
 */
public class ExecutionMethodCall extends AbstractExecutionStateNode<MethodBodyStatement> implements IExecutionMethodCall {
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public ExecutionMethodCall(Node proofNode) {
      super(proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected String lazyComputeName() {
      return getMethodReference().toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public MethodReference getMethodReference() {
      return getActiveStatement().getMethodReference();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ProgramMethod getProgramMethod() {
      return getActiveStatement().getProgramMethod(getServices());
   }
}
