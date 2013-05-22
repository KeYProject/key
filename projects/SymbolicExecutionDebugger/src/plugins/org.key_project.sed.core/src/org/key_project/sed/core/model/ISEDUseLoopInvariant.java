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

package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDUseLoopInvariant;
import org.key_project.sed.core.model.memory.SEDMemoryUseLoopInvariant;

/**
 * A node in the symbolic execution tree which represents a use of a loop invariant.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDUseLoopInvariant} instead of implementing this
 * interface directly. {@link SEDMemoryUseLoopInvariant} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDUseLoopInvariant extends ISEDDebugNode, IStackFrame {
   /**
    * Checks if the loop invariant is initially valid.
    * @return {@code true} initially valid, {@code false} initially invalid.
    */
   public boolean isInitiallyValid();
}