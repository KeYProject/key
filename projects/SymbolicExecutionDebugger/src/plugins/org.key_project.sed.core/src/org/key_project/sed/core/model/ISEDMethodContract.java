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
import org.key_project.sed.core.model.impl.AbstractSEDMethodContract;
import org.key_project.sed.core.model.memory.SEDMemoryMethodContract;

/**
 * A node in the symbolic execution tree which represents a use of an method contract.
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDMethodContract} instead of implementing this
 * interface directly. {@link SEDMemoryMethodContract} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ISEDDebugNode
 */
public interface ISEDMethodContract extends ISEDDebugNode, IStackFrame {
   /**
    * Checks if the precondition is complied.
    * @return {@code true} precondition complied, {@code false} precondition not complied.
    */
   public boolean isPreconditionComplied(); 

   /**
    * Checks if a not null check is available (instance method) or not (static method or constructor).
    * @return {@code true} not null check available, {@code false} not null check is not available.
    */
   public boolean hasNotNullCheck();
   
   /**
    * Checks if the not null check is complied.
    * @return {@code true} not null check complied, {@code false} not null check not complied.
    */
   public boolean isNotNullCheckComplied();
}