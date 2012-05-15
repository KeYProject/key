package org.key_project.sed.key.core.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.key.core.symbolic_execution.model.IExecutionNode;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;

/**
 * Provides a basic implementation of {@link IExecutionNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionNode implements IExecutionNode {
   /**
    * Reference to the parent {@link IExecutionNode}.
    */
   private AbstractExecutionNode parent;
   
   /**
    * Contains all child {@link IExecutionNode}s.
    */
   private List<IExecutionNode> children = new LinkedList<IExecutionNode>();

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
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionNode(Node proofNode) {
      assert proofNode != null;
      this.proofNode = proofNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public AbstractExecutionNode getParent() {
      return parent;
   }
   
   /**
    * Sets the parent {@link AbstractExecutionNode}.
    * @param parent The parent {@link AbstractExecutionNode} to set.
    */
   public void setParent(AbstractExecutionNode parent) {
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public AbstractExecutionNode[] getChildren() {
      return children.toArray(new AbstractExecutionNode[children.size()]);
   }

   /**
    * Adds a new child {@link AbstractExecutionNode}.
    * @param child A new child {@link AbstractExecutionNode}.
    */
   public void addChild(AbstractExecutionNode child) {
      if (child != null) {
         children.add(child);
      }
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
   public String getName() {
      if (name == null) {
         name = lazyComputeName();
      }
      return name;
   }

   /**
    * Computes the name of this node lazily when {@link #getName()}
    * is called the first time.
    * @return The human readable name of this {@link IExecutionNode}.
    */
   protected abstract String lazyComputeName();
}
