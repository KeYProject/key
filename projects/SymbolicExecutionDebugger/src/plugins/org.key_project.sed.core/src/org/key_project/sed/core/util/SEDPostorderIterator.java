/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Iterates postorder over the whole sub tree of a given {@link ISEDDebugElement}.
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
 * @see ISEDIterator
 */
public class SEDPostorderIterator implements ISEDIterator {
   /**
    * The element at that the iteration has started used as end condition
    * to make sure that only over the subtree of the element is iterated.
    */
   private ISEDDebugElement start;

   /**
    * The next element or {@code null} if no more elements exists.
    */
   private ISEDDebugElement next;
   
   /**
    * Constructor.
    * @param start The {@link ISEDDebugElement} to iterate over its sub tree.
    * @throws DebugException Occurred Exception.
    */
   public SEDPostorderIterator(ISEDDebugElement start) throws DebugException {      
      this.start = start;
      this.next = findMostLeftLeaf(start);
   }
   
   protected ISEDDebugElement findMostLeftLeaf(ISEDDebugElement start) throws DebugException {
      // Define entry point to start left leaf search
      ISEDDebugElement leftLeaf;
      if (start instanceof ISEDDebugTarget) {
         ISEDThread[] threads = ((ISEDDebugTarget)start).getSymbolicThreads(); 
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
      boolean done = !(leftLeaf instanceof ISEDDebugNode);
      while (!done) {
         ISEDDebugNode[] children = ((ISEDDebugNode)leftLeaf).getChildren(); 
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
   public ISEDDebugElement next() throws DebugException {
      ISEDDebugElement oldNext = next;
      updateNext();
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    * @throws DebugException Occurred Exception.
    */
   protected void updateNext() throws DebugException {
      ISEDDebugElement newNext = null;
      if (next instanceof ISEDDebugTarget) {
         newNext = null; // Debug target must be the last element
      }
      else if (next instanceof ISEDDebugNode) {
         newNext = getNextOnParent((ISEDDebugNode)next);
      }
      this.next = newNext;
   }
   
   /**
    * Returns the next element to select if all children of the given
    * {@link ISEDDebugNode} are visited.
    * @param node The visited {@link ISEDDebugNode}.
    * @return The next {@link ISEDDebugElement} to visit.
    * @throws DebugException Occurred Exception.
    */
   protected ISEDDebugElement getNextOnParent(ISEDDebugNode node) throws DebugException {
      ISEDDebugNode parent = node.getParent();
      // Search next debug node
      while (parent instanceof ISEDDebugNode && node != start) {
         ISEDDebugNode[] parentChildren = parent.getChildren();
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
      if (node instanceof ISEDThread && node != start) {
         ISEDThread[] parentChildren = node.getDebugTarget().getSymbolicThreads();
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