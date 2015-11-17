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

package org.key_project.sed.core.model.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISEValue;
import org.key_project.sed.core.model.ISEVariable;

/**
 * Provides a basic implementation of {@link ISEValue}.
 * @author Martin Hentschel
 * @see ISEValue
 */
public abstract class AbstractSEValue extends AbstractSEDebugElement implements ISEValue {
   /**
    * The parent {@link ISEVariable}.
    */
   private final ISEVariable parent;
   
   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this element is contained.
    * @param parent The parent {@link ISEVariable}.
    */
   public AbstractSEValue(ISEDebugTarget target, ISEVariable parent) {
      super(target);
      Assert.isNotNull(parent);
      this.parent = parent;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasVariables() throws DebugException {
      IVariable[] variables = getVariables();
      return variables != null && variables.length >= 1;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEVariable getParent() {
      return parent;
   }
}