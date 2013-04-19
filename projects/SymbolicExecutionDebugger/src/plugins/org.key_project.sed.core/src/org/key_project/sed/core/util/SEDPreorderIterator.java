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
 * Iterates preorder over the whole sub tree of a given {@link ISEDDebugElement}.
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
public class SEDPreorderIterator implements ISEDIterator {
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
    */
   public SEDPreorderIterator(ISEDDebugElement start) {      
      this.start = start;
      this.next = start;
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
         ISEDDebugTarget target = (ISEDDebugTarget)next;
         ISEDThread[] threads = target.getSymbolicThreads();
         if (!ArrayUtil.isEmpty(threads)) {
            newNext = threads[0];
         }
      }
      else if (next instanceof ISEDDebugNode) {
         ISEDDebugNode node = (ISEDDebugNode)next;
         ISEDDebugNode[] children = node.getChildren();
         if (!ArrayUtil.isEmpty(children)) {
            newNext = children[0];
         }
         else {
            newNext = getNextOnParent(node);
         }
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
      while (parent instanceof ISEDDebugNode) {
         ISEDDebugNode[] parentChildren = parent.getChildren();
         int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
         if (nodeIndex < 0) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Parent node \"" + parent + "\" does not contain child \"" + node + "."));
         }
         if (nodeIndex + 1 < parentChildren.length) {
            if (parentChildren[nodeIndex] != start) {
               return parentChildren[nodeIndex + 1];
            }
            else {
               return null;
            }
         }
         else {
            if (parentChildren[parentChildren.length - 1] != start) {
               node = parent;
               parent = parent.getParent(); // Continue search on parent without recursive call!
            }
            else {
               return null;
            }
         }
      }
      // Search of debug node failed, try to search next thread
      if (node instanceof ISEDThread) {
         ISEDThread[] parentChildren = node.getDebugTarget().getSymbolicThreads();
         int nodeIndex = ArrayUtil.indexOf(parentChildren, node);
         if (nodeIndex < 0) {
            throw new DebugException(LogUtil.getLogger().createErrorStatus("Debug target \"" + parent + "\" does not contain thread \"" + node + "."));
         }
         if (nodeIndex + 1 < parentChildren.length) {
            if (parentChildren[nodeIndex] != start) {
               return parentChildren[nodeIndex + 1];
            }
            else {
               return null;
            }
         }
         else {
            return null; // End of model reached.
         }
      }
      else {
         return null; // Search failed, no more elements available.
      }
   }
}