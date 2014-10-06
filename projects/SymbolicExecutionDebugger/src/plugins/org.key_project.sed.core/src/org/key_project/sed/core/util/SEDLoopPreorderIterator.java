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

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopStatement;
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
public class SEDLoopPreorderIterator implements ISEDIterator {
   /**
    * The element at that the iteration has started used as end condition
    * to make sure that only over the subtree of the element is iterated.
    */
   private ISEDLoopStatement start;

   /**
    * The next element or {@code null} if no more elements exists.
    */
   private ISEDDebugNode next;
   
   /**
    * The Set of last {@link ISEDLoopCondition}s of the Loop
    */
   private LinkedList<ISEDLoopCondition> loopLeafs;
   
   /**
    * LoopLeaf of the current branch
    */
   private ISEDLoopCondition currentLoopLeaf; 
   
   /**
    * Current Iteration
    */
   private int iteration;
   
   /**
    * Amount which changes the iteration (backtrack)
    */
   private int changeAmount;
   
   /**
    * To change or not to change
    */
   private boolean change = false;
   
   /**
    * Constructor.
    * @param start The {@link ISEDDebugElement} to iterate over its sub tree.
    * @throws DebugException 
    */
   public SEDLoopPreorderIterator(ISEDLoopStatement start) throws DebugException {      
      this.start = start;
      this.next = start;
      loopLeafs = gatherLoopLeafs();
      iteration = 0;
      changeAmount = 0;
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
      
      if(change) {
         iteration -= changeAmount;
         changeAmount = 0;
         change = false;
      }
      
      if(changeAmount > 0) {
         change = true;
      }
      
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    * @throws DebugException Occurred Exception.
    */
   protected void updateNext() throws DebugException {
      ISEDDebugNode newNext = null;
      if (next instanceof ISEDDebugNode) {
         ISEDDebugNode node = (ISEDDebugNode)next;
         ISEDDebugNode[] children = NodeUtil.getChildren(node, true);
         if (!ArrayUtil.isEmpty(children) && !loopLeafs.contains(children[0])) {
            newNext = children[0];
            
            if(next instanceof ISEDLoopCondition) {
               iteration++;
            }
         }
         else {
            if (!ArrayUtil.isEmpty(children) && loopLeafs.contains(children[0])) {
               currentLoopLeaf = (ISEDLoopCondition) children[0];
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
   private ISEDDebugNode getNextOnParent(ISEDDebugNode node) throws DebugException {
      ISEDDebugNode parent = NodeUtil.getParent(node);
      // Search next debug node
      while (parent instanceof ISEDDebugNode) {
         ISEDDebugNode[] parentChildren = NodeUtil.getChildren(parent, true);
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
               if(node instanceof ISEDLoopCondition) {
                  changeAmount++;
//                  iteration--;
               }
               
               node = parent;
               parent = NodeUtil.getParent(parent);// Continue search on parent without recursive call!
            }
            else {
               return null;
            }
         }
      }

      return null;
   }
   
   private LinkedList<ISEDLoopCondition> gatherLoopLeafs() throws DebugException {
      LinkedList<ISEDLoopCondition> loopLeafs = new LinkedList<ISEDLoopCondition>();
      
      ISEDDebugNode next = start;
      ISEDLoopCondition condition = null;
      
      while(next != null) {
         ISEDDebugNode[] children = NodeUtil.getChildren(next);
         if (!ArrayUtil.isEmpty(children)) {
            next = children[0];
            
            if(next instanceof ISEDLoopCondition) {
               condition = (ISEDLoopCondition) next;
            }
         }
         else {
            if(condition != null) {
               loopLeafs.add(condition);
               condition = null;
            }
            
            next = getNextOnParent(next);
         }
      }
      
      return loopLeafs;
   }
   
   public LinkedList<ISEDLoopCondition> getLoopLeafs() {
      return loopLeafs;
   }
   
   public int getIteration() {
      return iteration;
   }
   
   public ISEDLoopCondition getCurrentLoopLeaf() {
      return currentLoopLeaf;
   }
}