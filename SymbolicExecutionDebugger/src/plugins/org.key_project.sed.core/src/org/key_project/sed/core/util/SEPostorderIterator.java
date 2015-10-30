/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.core.util;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Iterates postorder over the whole sub tree of a given {@link ISEDebugElement}.
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
 * @see ISEIterator
 */
public class SEPostorderIterator implements ISEIterator {
   /**
    * The element at that the iteration has started used as end condition
    * to make sure that only over the subtree of the element is iterated.
    */
   private ISEDebugElement start;

   /**
    * The next element or {@code null} if no more elements exists.
    */
   private ISEDebugElement next;
   
   /**
    * Constructor.
    * @param start The {@link ISEDebugElement} to iterate over its sub tree.
    * @throws DebugException Occurred Exception.
    */
   public SEPostorderIterator(ISEDebugElement start) throws DebugException {      
      this.start = start;
      this.next = findMostLeftLeaf(start);
   }
   
   protected ISEDebugElement findMostLeftLeaf(ISEDebugElement start) throws DebugException {
      // Define entry point to start left leaf search
      ISEDebugElement leftLeaf;
      if (start instanceof ISEDebugTarget) {
         ISEThread[] threads = ((ISEDebugTarget)start).getSymbolicThreads(); 
         if (!ArrayUtil.isEmpty(threads)) {
            leftLeaf = threads[0];
         }
         else {
            leftLeaf = start;
         }
      }
      else {
         leftLeaf = start;
      }
      // Search left leaf
      boolean done = !(leftLeaf instanceof ISENode);
      while (!done) {
         ISENode[] children = ((ISENode)leftLeaf).getChildren(); 
         if (!ArrayUtil.isEmpty(children)) {
            leftLeaf = children[0];
         }
         else {
            done = true;
         }
      }
      return leftLeaf;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasNext() throws DebugException {
      return next != null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDebugElement next() throws DebugException {
      ISEDebugElement oldNext = next;
      updateNext();
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    * @throws DebugException Occurred Exception.
    */
   protected void updateNext() throws DebugException {
      ISEDebugElement newNext = null;
      if (next instanceof ISEDebugTarget) {
         newNext = null; // Debug target must be the last element
      }
      else if (next instanceof ISENode) {
         newNext = getNextOnParent((ISENode)next);
      }
      this.next = newNext;
   }
   
   /**
    * Returns the next element to select if all children of the given
    * {@link ISENode} are visited.
    * @param node The visited {@link ISENode}.
    * @return The next {@link ISEDebugElement} to visit.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDebugElement getNextOnParent(ISENode node) throws DebugException {
      ISENode parent = node.getParent();
      // Search next debug node
      while (parent instanceof ISENode && node != start) {
         ISENode[] parentChildren = parent.getChildren();
         int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
         if (nodeIndex < 0) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Parent node \"" + parent + "\" does not contain child \"" + node + "."));
         }
         if (nodeIndex + 1 < parentChildren.length) {
            return findMostLeftLeaf(parentChildren[nodeIndex + 1]);
         }
         else {
            if (parentChildren[parentChildren.length - 1] != start) {
               return parent;
            }
            else {
               node = parent;
               parent = parent.getParent(); // Continue search on parent without recursive call!
            }
         }
      }
      // Search of debug node failed, try to search next thread
      if (node instanceof ISEThread && node != start) {
         ISEThread[] parentChildren = node.getDebugTarget().getSymbolicThreads();
         int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
         if (nodeIndex < 0) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Debug target \"" + parent + "\" does not contain thread \"" + node + "."));
         }
         if (nodeIndex + 1 < parentChildren.length) {
            return findMostLeftLeaf(parentChildren[nodeIndex + 1]);
         }
         else {
            return node.getDebugTarget(); // End of model reached.
         }
      }
      else {
         return null; // Search failed, no more elements available.
      }
   }
}