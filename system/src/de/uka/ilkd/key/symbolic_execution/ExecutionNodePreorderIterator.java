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

package de.uka.ilkd.key.symbolic_execution;

import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;

/**
 * <p>
 * Iterates preorder over the whole sub tree of a given {@link IExecutionNode}.
 * </p>
 * <p>
 * Instances of this class should always be used instead of recursive method
 * calls because they cause {@link StackOverflowError}s even in small programs.
 * </p>
 * <p>
 * <b>Attention: </b>The iteration process does not take care of changes in
 * the model. If the containment hierarchy changes during iteration it is possible
 * that elements are left or visited multiple times. For this reason it is forbidden
 * to change the model during iteration. But the developer has to take care about it.
 * </p>
 * @author Martin Hentschel
 */
public class ExecutionNodePreorderIterator {
   /**
    * The element at that the iteration has started used as end condition
    * to make sure that only over the subtree of the element is iterated.
    */
   private IExecutionNode start;

   /**
    * The next element or {@code null} if no more elements exists.
    */
   private IExecutionNode next;
   
   /**
    * Constructor.
    * @param start The {@link IExecutionNode} to iterate over its sub tree.
    */
   public ExecutionNodePreorderIterator(IExecutionNode start) {      
      this.start = start;
      this.next = start;
   }
   
   /**
    * Checks if more elements are available.
    * @return {@code true} has more elements, {@code false} has not more elements.
    */
   public boolean hasNext() {
      return next != null;
   }
   
   /**
    * Returns the next {@link IExecutionNode} in the containment hierarchy.
    * @return The next {@link IExecutionNode}.
    */
   public IExecutionNode next() {
      IExecutionNode oldNext = next;
      updateNext();
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    */
   protected void updateNext() {
      IExecutionNode newNext = null;
      IExecutionNode[] children = next.getChildren();
      if (children.length >= 1) {
         newNext = children[0];
      }
      else {
         newNext = getNextOnParent(next);
      }
      this.next = newNext;
   }
   
   /**
    * Returns the next element to select if all children of the given
    * {@link IExecutionNode} are visited.
    * @param node The visited {@link IExecutionNode}.
    * @return The next {@link IExecutionNode} to visit.
    */
   protected IExecutionNode getNextOnParent(IExecutionNode node) {
      IExecutionNode parent = node.getParent();
      while (parent != null) {
         boolean IExecutionNodeFound = false; // Indicates that IExecutionNode was found on the parent.
         IExecutionNode[] children = parent.getChildren();
         IExecutionNode nextChildOnParent = null; // The next child on the parent or the last child after iteration has finished
         for (int i = 0; i < children.length; i++) {
            nextChildOnParent = children[i];
            if (nextChildOnParent == start) {
               return null;
            }
            if (IExecutionNodeFound) {
               return nextChildOnParent;
            }
            if (nextChildOnParent == node) {
               IExecutionNodeFound = true;
            }
         }
         if (nextChildOnParent != start) {
            node = parent; // Continue search on parent without recursive call!
            parent = parent.getParent();
         }
         else {
            return null;
         }
      }
      return null; // No more parents available.
   }
}