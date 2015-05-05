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
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;
import org.key_project.util.java.ArrayUtil;

/**
 * <p>
 * Iterates preorder over the whole group of a given {@link ISEDGroupable}.
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
 * @author Martin Möller
 * @see ISEDIterator
 */
public class SEDGroupPreorderIterator implements ISEDIterator {
   /**
    * The element at that the iteration has started used as end condition
    * to make sure that only over the subtree of the element is iterated.
    */
   private ISEDDebugNode start;

   /**
    * The next element or {@code null} if no more elements exists.
    */
   private ISEDDebugNode next;
   
   /**
    * The group to iterate over
    */
   private ISEDGroupable groupStart;
   
   /**
    * States if all branches of the group are finished or not
    */
   boolean allBranchesFinished = true;
   
   /**
    * Constructor.
    * @param start The {@link ISEDGroupable} to iterate over its group and
    * additionally the node where the iteration begins.
    */
   public SEDGroupPreorderIterator(ISEDGroupable start) {
      this.start = (ISEDDebugNode) start;
      this.next = (ISEDDebugNode) start;
      this.groupStart = start;
   }
   
   /**
    * Constructor.
    * @param group The {@link ISEDGroupable} to iterate over its group.
    * @param start The node within the group where the iteration begins.
    * @param stopAtStart Determines if the iteration takes place only in the subtree of the start node ({@code true},
    * or in the whole group {@code false}.
    */
   public SEDGroupPreorderIterator(ISEDGroupable group, ISEDDebugNode start, boolean stopAtStart) {
      this.start = stopAtStart ? start : (ISEDDebugNode) group;
      this.next = start;
      this.groupStart = group;
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
   public ISEDDebugNode next() throws DebugException {
      ISEDDebugNode oldNext = next;
      boolean groupEndReached = false;
      
      if(oldNext.getGroupStartCondition((ISEDDebugNode) groupStart) != null) {
         groupEndReached = true;
      }
      
      updateNext(groupEndReached);
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    * @throws DebugException Occurred Exception.
    */
   protected void updateNext(boolean groupEndReached) throws DebugException {
      ISEDDebugNode newNext = null;
      if (next instanceof ISEDDebugNode) {
         ISEDDebugNode node = (ISEDDebugNode)next;
         ISEDDebugNode[] children = NodeUtil.getChildren(node);
         if (!ArrayUtil.isEmpty(children) && !groupEndReached) {
//            if(ArrayUtil.isEmpty(children[0].getCallStack()) && !(children[0] instanceof ISEDBranchCondition)) {
//               newNext = getNextOnParent(node);
//            }
//            else {
               newNext = children[0];
//            }
         }
         else {
            if(!groupEndReached) {
               allBranchesFinished = false;
            }

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
   protected ISEDDebugNode getNextOnParent(ISEDDebugNode node) throws DebugException {
      ISEDDebugNode parent = NodeUtil.getParent(node);
      // Search next debug node
      while (parent instanceof ISEDDebugNode) {
         ISEDDebugNode[] parentChildren = NodeUtil.getChildren(parent);
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
               parent = NodeUtil.getParent(parent); // Continue search on parent without recursive call!
            }
            else {
               return null;
            }
         }
      }
      
      return null;
   }
   
   /**
    * Determines if all branches of the group are finished (True) or not (False).
    * @return True if all branches of the group are finished, False otherwise.
    * @throws DebugException Occured Exception.
    */
   public boolean allBranchesFinished() throws DebugException {
      while(hasNext()) {
         next();
         // No need to visit the rest of the group
         if(!allBranchesFinished) {
            return false;
         }
      }
      
      return true;
   }
}