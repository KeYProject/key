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
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;

/**
 * Provides a basic implementation of {@link ISEDValue}.
 * @author Martin Hentschel
 * @see ISEDValue
 */
public abstract class AbstractSEDValue extends AbstractSEDDebugElement implements ISEDValue {
   /**
    * The parent {@link ISEDVariable}.
    */
   private final ISEDVariable parent;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    * @param parent The parent {@link ISEDVariable}.
    */
   public AbstractSEDValue(ISEDDebugTarget target, ISEDVariable parent) {
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
   public ISEDVariable getParent() {
      return parent;
   }
}