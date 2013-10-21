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

package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;

/**
 * Defines the public methods to edit an {@link ISEDDebugTarget} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryDebugTarget extends ISEDDebugTarget {
   /**
    * Adds a new {@link ISEDThread}.
    * @param thread The {@link ISEDThread} to add.
    */
   public void addSymbolicThread(ISEDThread thread);

   /**
    * Adds a new {@link ISEDThread}.
    * @param index The index to insert the new thread at.
    * @param thread The {@link ISEDThread} to add.
    */
   public void addSymbolicThread(int index, ISEDThread thread);
   
   /**
    * Removes the child {@link ISEDThread}.
    * @param thread The {@link ISEDThread} to remove.
    */
   public void removeSymbolicThread(ISEDThread thread);
   
   /**
    * Returns the index of the given child {@link ISEDThread}.
    * @param thread The child {@link ISEDThread}.
    * @return The index of the child {@link ISEDThread} or {@code -1} if it is no child.
    */
   public int indexOfSymbolicThread(ISEDThread thread);
}