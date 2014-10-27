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

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.key_project.sed.core.model.impl.AbstractSEDMethodCall;
import org.key_project.sed.core.model.memory.SEDMemoryMethodCall;

/**
 * A node in the symbolic execution tree which represents a method call,
 * e.g. {@code foo()}.
 * <p>
 * A symbolic method call is also a normal stack frame ({@link IStackFrame})
 * for compatibility reasons with the Eclipse debug API.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDMethodCall} instead of implementing this
 * interface directly. {@link SEDMemoryMethodCall} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDMethodCall extends ISEDDebugNode, IStackFrame, ISEDGroupable {
   /**
    * Returns the up to know discovered conditions when this {@link ISEDMethodCall} returns.
    * @return The up to know discovered conditions when this {@link ISEDMethodCall} returns.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDBranchCondition[] getMethodReturnConditions() throws DebugException;
}