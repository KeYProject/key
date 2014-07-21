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

import java.util.UUID;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.model.DebugElement;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * Provides a basic implementation of {@link ISEDDebugElement}.
 * @author Martin Hentschel
 * @see ISEDDebugElement
 */
public abstract class AbstractSEDDebugElement extends DebugElement implements ISEDDebugElement {
   /**
    * The unique ID.
    */
   private String id;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in that this element is contained.
    */
   public AbstractSEDDebugElement(ISEDDebugTarget target) {
      super(target);
   }

   /**
    * Computes a new unique ID which is "_" + UUID. The "_" is used
    * to make the ID a valid XML name.
    * @return A new computed ID.
    */
   public static String computeNewId() {
      return "_" + UUID.randomUUID().toString();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugTarget getDebugTarget() {
      return (ISEDDebugTarget)super.getDebugTarget();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getModelIdentifier() {
      return getDebugTarget().getModelIdentifier();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getId() {
      if (id == null) {
         synchronized (this) {
            if (id == null) {
               id = computeNewId();
            }
         }
      }
      return id;
   }

   /**
    * Sets the unique ID.
    * @param id The new unique ID to use.
    */
   protected void setId(String id) {
      Assert.isTrue(this.id == null, "Can't change an already existing ID.");
      this.id = id;
   }
}