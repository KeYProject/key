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
import org.key_project.sed.core.model.impl.AbstractSELoopStatement;
import org.key_project.sed.core.model.memory.SEMemoryLoopStatement;

/**
 * A node in the symbolic execution tree which represents a loop.
 * e.g. {@code while(x >= 0)}. The loop condition ({@code x >= 0}) itself 
 * is represented as {@link ISELoopCondition} node.
 * <p>
 * A symbolic loop statement is also a normal stack frame ({@link IStackFrame})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSELoopStatement} instead of implementing this
 * interface directly. {@link SEMemoryLoopStatement} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISENode
 */
public interface ISELoopStatement extends ISENode, IStackFrame, ISEGroupable {

}