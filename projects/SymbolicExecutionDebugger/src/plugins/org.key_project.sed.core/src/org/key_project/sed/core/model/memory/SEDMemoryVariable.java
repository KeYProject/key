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

package org.key_project.sed.core.model.memory;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IValue;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.core.model.impl.AbstractSEDVariable;

/**
 * Implementation of {@link ISEDVariable} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryVariable extends AbstractSEDVariable {
   /**
    * The contained {@link IValue}.
    */
   private IValue value;

   /**
    * The name.
    */
   private String name;
   
   /**
    * The reference type name.
    */
   private String referenceTypeName;

   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    */
   public SEDMemoryVariable(ISEDDebugTarget target) {
      super(target);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IValue getValue() throws DebugException {
      return value;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getReferenceTypeName() throws DebugException {
      return referenceTypeName;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasValueChanged() throws DebugException {
      return false;
   }

   /**
    * Sets the contained {@link IValue}.
    * @param value The {@link IValue} to set.
    */
   public void setValue(IValue value) {
      this.value = value;
   }

   /**
    * Sets the name.
    * @param name The name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * Sets the reference type name.
    * @param referenceTypeName The reference type name to set.
    */
   public void setReferenceTypeName(String referenceTypeName) {
      this.referenceTypeName = referenceTypeName;
   }
}