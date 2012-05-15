package org.key_project.sed.key.core.symbolic_execution.model.impl;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;
import org.key_project.sed.key.core.symbolic_execution.model.IExecutionStateNode;

import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.proof.Node;

/**
 * Provides a basic implementation of {@link IExecutionStateNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionStateNode<S extends SourceElement> extends AbstractExecutionNode implements IExecutionStateNode<S> {
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
}
