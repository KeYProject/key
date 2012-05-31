package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;

/**
 * Provides a basic implementation of {@link IExecutionStateNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionStateNode<S extends SourceElement> extends AbstractExecutionNode implements IExecutionStateNode<S> {
   /**
    * The variable value pairs of the current state.
    */
   private IExecutionVariable[] variables;
   
   /**
    * Constructor.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionStateNode(Node proofNode) {
      super(proofNode);
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("unchecked")
   @Override
   public S getActiveStatement() {
      return (S)getProofNodeInfo().getActiveStatement();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public PositionInfo getActivePositionInfo() {
      return getActiveStatement().getPositionInfo();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionVariable[] getVariables() {
      if (variables == null) {
         variables = lazyComputeVariables();
      }
      return variables;
   }

   /**
    * Computes the variables lazily when {@link #getVariables()} is 
    * called the first time.
    * @return The {@link IExecutionVariable}s of the current state.
    */
   protected abstract IExecutionVariable[] lazyComputeVariables();
}
