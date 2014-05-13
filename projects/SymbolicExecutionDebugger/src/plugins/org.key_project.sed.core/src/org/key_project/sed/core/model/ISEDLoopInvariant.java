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

package org.key_project.sed.core.model;

import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDLoopInvariant;
import org.key_project.sed.core.model.memory.SEDMemoryLoopInvariant;

/**
 * A node in the symbolic execution tree which represents a use of a loop invariant.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDLoopInvariant} instead of implementing this
 * interface directly. {@link SEDMemoryLoopInvariant} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDLoopInvariant extends ISEDDebugNode, IStackFrame {
   /**
    * Checks if the loop invariant is initially valid.
    * @return {@code true} initially valid, {@code false} initially invalid.
    */
   public boolean isInitiallyValid();
}