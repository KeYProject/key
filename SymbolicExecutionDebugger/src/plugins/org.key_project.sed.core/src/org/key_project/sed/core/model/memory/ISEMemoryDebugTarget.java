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

import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEThread;

/**
 * Defines the public methods to edit an {@link ISEDebugTarget} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEMemoryDebugTarget extends ISEDebugTarget {
   /**
    * Adds a new {@link ISEThread}.
    * @param thread The {@link ISEThread} to add.
    */
   public void addSymbolicThread(ISEThread thread);

   /**
    * Adds a new {@link ISEThread}.
    * @param index The index to insert the new thread at.
    * @param thread The {@link ISEThread} to add.
    */
   public void addSymbolicThread(int index, ISEThread thread);
   
   /**
    * Removes the child {@link ISEThread}.
    * @param thread The {@link ISEThread} to remove.
    */
   public void removeSymbolicThread(ISEThread thread);
   
   /**
    * Returns the index of the given child {@link ISEThread}.
    * @param thread The child {@link ISEThread}.
    * @return The index of the child {@link ISEThread} or {@code -1} if it is no child.
    */
   public int indexOfSymbolicThread(ISEThread thread);
}