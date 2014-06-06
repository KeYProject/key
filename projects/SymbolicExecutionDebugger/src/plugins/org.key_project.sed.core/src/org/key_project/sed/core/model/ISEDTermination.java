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
import org.eclipse.debug.core.model.ITerminate;
import org.key_project.sed.core.model.impl.AbstractSEDTermination;
import org.key_project.sed.core.model.memory.SEDMemoryTermination;

/**
 * A node in the symbolic execution tree which represents the normal termination of a branch,
 * e.g. {@code <end>}.
 * <p>
 * A symbolic termination is also a normal stack frame ({@link IStackFrame})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDTermination} instead of implementing this
 * interface directly. {@link SEDMemoryTermination} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDTermination extends ISEDDebugNode, ITerminate {
   /**
    * Checks if this branch is verified.
    * @return {@code true} verified, {@code false} not verified.
    */
   public boolean isVerified();
}