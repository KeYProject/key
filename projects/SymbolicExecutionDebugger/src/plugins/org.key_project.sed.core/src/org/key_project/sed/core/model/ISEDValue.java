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
import org.eclipse.debug.core.model.IValue;
import org.key_project.sed.core.model.impl.AbstractSEDValue;
import org.key_project.sed.core.model.memory.SEDMemoryValue;

/**
 * A value of a variable of a node in the symbolic execution tree,
 * e.g. the method call parameter {@code int a} which has value {@code 42}.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDValue} instead of implementing this
 * interface directly. {@link SEDMemoryValue} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDValue extends IValue, ISEDDebugElement {
   /**
    * Checks if the represented value is an object.
    * @return {@code true} value is object, {@code false} value is object attribute.
    * @throws DebugException Occurred Exception.
    */
   public boolean isObject() throws DebugException;
   
   /**
    * Checks if this value is single or multi valued (case of multiple conditional values).
    * @return {@code true} multi valued, {@code false} single valued.
    * @throws DebugException Occurred Exception.
    */
   public boolean isMultiValued() throws DebugException;
}