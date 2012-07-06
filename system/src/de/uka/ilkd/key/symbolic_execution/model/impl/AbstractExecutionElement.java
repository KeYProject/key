package de.uka.ilkd.key.symbolic_execution.model.impl;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionElement;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Provides a basic implementation of {@link IExecutionElement}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionElement implements IExecutionElement {
   /**
    * The used {@link KeYMediator} during proof.
    */
   private KeYMediator mediator;

   /**
    * The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   private Node proofNode;
   
   /**
    * The human readable name of this node.
    */
   private String name;
   
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionElement(KeYMediator mediator, Node proofNode) {
      assert mediator != null;
      assert proofNode != null;
      this.mediator = mediator;
      this.proofNode = proofNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYMediator getMediator() {
      return mediator;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Services getServices() {
      return getProof().getServices();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getProof() {
      return getProofNode().proof();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Node getProofNode() {
      return proofNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public NodeInfo getProofNodeInfo() {
      return getProofNode().getNodeInfo();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws ProofInputException {
      synchronized (this) {
         if (name == null) {
            name = lazyComputeName();
         }
         return name;
      }
   }

   /**
    * Computes the name of this node lazily when {@link #getName()}
    * is called the first time.
    * @return The human readable name of this {@link IExecutionNode}.
    */
   protected abstract String lazyComputeName() throws ProofInputException;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      try {
         return getElementType() + " " + getName();
      }
      catch (ProofInputException e) {
         return getElementType() + " " + e.getMessage();
      }
   }
}
