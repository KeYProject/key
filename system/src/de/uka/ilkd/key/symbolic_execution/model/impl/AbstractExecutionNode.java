// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.symbolic_execution.model.impl;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.ITreeSettings;

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
   private final List<IExecutionNode> children = new LinkedList<IExecutionNode>();
   
   /**
    * The contained call stack.
    */
   private IExecutionNode[] callStack;
   
   /**
    * Constructor.
    * @param settings The {@link ITreeSettings} to use.
    * @param mediator The used {@link KeYMediator} during proof.
    * @param proofNode The {@link Node} of KeY's proof tree which is represented by this {@link IExecutionNode}.
    */
   public AbstractExecutionNode(ITreeSettings settings,
                                KeYMediator mediator, 
                                Node proofNode) {
      super(settings, mediator, proofNode);
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
      return result != null ? result : getServices().getTermBuilder().tt();
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
      return result != null ? result : getServices().getTermBuilder().tt().toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IExecutionNode[] getCallStack() {
      return callStack;
   }
   
   /**
    * Sets the call stack.
    * @param callStack The call stack.
    */
   public void setCallStack(IExecutionNode[] callStack) {
      this.callStack = callStack;
   }
}