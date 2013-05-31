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

package de.hentschel.visualdbc.datasource.model.memory;

import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.IDSProvableReference;

/**
 * Default implementation for an {@link IDSProvableReference} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryProvableReference implements IDSProvableReference {
   /**
    * The reference target {@link IDSProvable}.
    */
   private IDSProvable targetProvable;
   
   /**
    * The human readable label.
    */
   private String label;

   /**
    * Default constructor.
    */
   public MemoryProvableReference() {
   }

   /**
    * Constructor.
    * @param targetProvable The reference target {@link IDSProvable}.
    * @param label The human readable label.
    */
   public MemoryProvableReference(IDSProvable targetProvable, String label) {
      setTargetProvable(targetProvable);
      setLabel(label);
   }

   /**
    * Sets the target {@link IDSProvable}.
    * @param targetProvable The target {@link IDSProvable} to set.
    */
   public void setTargetProvable(IDSProvable targetProvable) {
      this.targetProvable = targetProvable;
   }

   /**
    * Sets the human readable label.
    * @param label The label to set.
    */
   public void setLabel(String label) {
      this.label = label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSProvable getTargetProvable() {
      return targetProvable;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getLabel() {
      return label;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean equals(Object obj) {
      if (obj instanceof IDSProvableReference) {
         IDSProvableReference other = (IDSProvableReference)obj;
         return ObjectUtil.equals(this.getLabel(), other.getLabel()) &&
                ObjectUtil.equals(this.getTargetProvable(), other.getTargetProvable());
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int hashCode() {
      return ObjectUtil.hashCode(getLabel()) + 
             ObjectUtil.hashCode(getTargetProvable());
   }
}