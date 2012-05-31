package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodCall;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

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

   /**
    * {@inheritDoc}
    */
   @Override
   protected IExecutionVariable[] lazyComputeVariables() {
      return SymbolicExecutionUtil.createExecutionVariables(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getElementType() {
      return "Method Call";
   }
}
