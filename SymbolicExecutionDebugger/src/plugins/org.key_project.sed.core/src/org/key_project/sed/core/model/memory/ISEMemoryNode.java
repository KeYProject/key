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

package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISEConstraint;
import org.key_project.sed.core.model.ISENode;

/**
 * Defines the public methods to edit an {@link ISENode} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEMemoryNode extends ISENode {
   /**
    * Sets the unique ID.
    * @param id The new unique ID to use.
    */
   public void setId(String id);
   
   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   public void setName(String name);
   
   /**
    * Sets the path condition.
    * @param pathCondtion The path condition to set.
    */
   public void setPathCondition(String pathCondition);
   
   /**
    * Adds a new {@link ISENode} child node.
    * @param child The {@link ISENode} to add.
    */
   public void addChild(ISENode child);
   
   /**
    * Adds a new {@link ISENode} child node.
    * @param index The index to insert the new child at.
    * @param child The {@link ISENode} to add.
    */
   public void addChild(int index, ISENode child);
   
   /**
    * Removes the child {@link ISENode}.
    * @param child The {@link ISENode} to remove.
    */
   public void removeChild(ISENode child);
   
   /**
    * Returns the index of the given child {@link ISENode}.
    * @param child The child {@link ISENode}.
    * @return The index of the child {@link ISENode} or {@code -1} if it is no child.
    */
   public int indexOfChild(ISENode child);
   
   /**
    * Sets the call stack.
    * @param callStack The call stack to use.
    */
   public void setCallStack(ISENode[] callStack);
   
   /**
    * Adds a new {@link ISEConstraint}.
    * @param constraint The {@link ISEConstraint} to add.
    */
   public void addConstraint(ISEConstraint constraint);
   
   /**
    * Adds the given {@link ISEBranchCondition} as group start condition.
    * @param groupStartCondition The {@link ISEBranchCondition} to add.
    */
   public void addGroupStartCondition(ISEBranchCondition groupStartCondition);
}