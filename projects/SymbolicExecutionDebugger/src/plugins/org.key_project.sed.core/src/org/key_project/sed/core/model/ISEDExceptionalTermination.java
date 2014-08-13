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
import org.key_project.sed.core.model.impl.AbstractSEDExceptionalTermination;
import org.key_project.sed.core.model.memory.SEDMemoryExceptionalTermination;

/**
 * A node in the symbolic execution tree which represents an exceptional termination of a branch,
 * e.g. {@code <uncaught java.lang.NullPointerException>}.
 * <p>
 * A symbolic exceptional termination is also a normal stack frame ({@link IStackFrame})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDExceptionalTermination} instead of implementing this
 * interface directly. {@link SEDMemoryExceptionalTermination} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDExceptionalTermination extends ISEDTermination {

}