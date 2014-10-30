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
import org.key_project.sed.core.model.impl.AbstractSEDBranchCondition;
import org.key_project.sed.core.model.memory.SEDMemoryBranchCondition;

/**
 * A node in the symbolic execution tree which represents a branch condition,
 * e.g. {@code x < 0}.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDBranchCondition} instead of implementing this
 * interface directly. {@link SEDMemoryBranchCondition} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDBranchCondition extends ISEDDebugNode, IStackFrame {

}