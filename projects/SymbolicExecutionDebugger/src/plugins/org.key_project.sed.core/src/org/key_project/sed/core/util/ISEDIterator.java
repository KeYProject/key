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

/**
 * Defines the methods an iterator over the containment hierarchy
 * of {@link ISEDDebugElement}s needs.
 * @author Martin Hentschel
 * @see SEDPreorderIterator
 * @see SEDPostorderIterator
 */
public interface ISEDIterator {
   /**
    * Checks if more elements are available.
    * @return {@code true} has more elements, {@code false} has not more elements.
    * @throws DebugException Occurred Exception.
    */
   public boolean hasNext() throws DebugException;
   
   /**
    * Returns the next {@link ISEDDebugElement} in the containment hierarchy.
    * @return The next {@link ISEDDebugElement}.
    * @throws DebugException Occurred Exception.
    */
   public ISEDDebugElement next() throws DebugException;
}