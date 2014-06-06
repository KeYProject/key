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

import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.util.java.CollectionUtil;

/**
 * <p>
 * Iterates breadth first like over the whole sub tree of a given {@link ISEDDebugElement}.
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
public class SEDBreadthFirstIterator implements ISEDIterator {
   /**
    * The next elements on the current level.
    */
   private List<ISEDDebugElement> nextElements;

   /**
    * The previous elements on the last level.
    */
   private Iterator<ISEDDebugElement> nextIter;
   
   /**
    * Constructor.
    * @param start The {@link ISEDDebugElement} to iterate over its sub tree.
    */
   public SEDBreadthFirstIterator(ISEDDebugElement start) {
      if (start != null) {
         nextElements = Collections.singletonList(start);
         nextIter = nextElements.iterator();
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasNext() throws DebugException {
      return nextIter != null;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugElement next() throws DebugException {
      ISEDDebugElement next = nextIter.next();
      if (!nextIter.hasNext()) {
         List<ISEDDebugElement> newNextElements = new LinkedList<ISEDDebugElement>();
         for (ISEDDebugElement element : nextElements) {
            if (element instanceof ISEDDebugTarget) {
               ISEDDebugTarget target = (ISEDDebugTarget)element;
               CollectionUtil.addAll(newNextElements, target.getSymbolicThreads());
            }
            else if (element instanceof ISEDDebugNode) {
               ISEDDebugNode node = (ISEDDebugNode)element;
               CollectionUtil.addAll(newNextElements, node.getChildren());
            }
         }
         if (!newNextElements.isEmpty()) {
            nextElements = newNextElements;
            nextIter = newNextElements.iterator();
         }
         else {
            nextElements = null;
            nextIter = null;
         }
      }
      return next;
   }
}