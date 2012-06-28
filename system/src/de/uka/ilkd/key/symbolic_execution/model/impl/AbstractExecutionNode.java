package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * Provides a basic implementation of {@link IExecutionNode}.
 * @author Martin Hentschel
 */
public abstract class AbstractExecutionNode extends AbstractExecutionElement implements IExecutionNode {
   /**
    * Reference to the parent {@link IExecutionNode}.
    */
   private AbstractExecutionNode parent;
   
   /**
    * Contains all child {@link IExecutionNode}s.
    */
   private List<IExecutionNode> children = new LinkedList<IExecutionNode>();
   
   /**
    * Constructor.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionNode(KeYMediator mediator, Node proofNode) {
      super(mediator, proofNode);
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
   public boolean isPathConditionChanged() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Term getPathCondition() throws ProofInputException {
      // Search path condition of the parent which is used by default.
      Term result = null;
      AbstractExecutionNode parent = getParent();
      while (result == null && parent != null) {
         if (parent.isPathConditionChanged()) {
            result = parent.getPathCondition();
         }
         else {
            parent = parent.getParent();
         }
      }
      // Check if a path condition was found.
      return result != null ? result :  TermBuilder.DF.tt();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getFormatedPathCondition() throws ProofInputException {
      // Search path condition of the parent which is used by default.
      String result = null;
      AbstractExecutionNode parent = getParent();
      while (result == null && parent != null) {
         if (parent.isPathConditionChanged()) {
            result = parent.getFormatedPathCondition();
         }
         else {
            parent = parent.getParent();
         }
      }
      // Check if a path condition was found.
      return result != null ? result :  TermBuilder.DF.tt().toString();
   }
}
