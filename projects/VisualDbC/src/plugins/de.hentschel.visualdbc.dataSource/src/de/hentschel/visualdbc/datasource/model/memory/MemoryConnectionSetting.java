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

package de.hentschel.visualdbc.datasource.model.memory;

import org.eclipse.jface.viewers.ISelection;

import de.hentschel.visualdbc.datasource.model.IDSConnectionSetting;

/**
 * Default implementation for an {@link IDSConnectionSetting} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryConnectionSetting implements IDSConnectionSetting {
   /**
    * The key.
    */
   private String key;
   
   /**
    * The name.
    */
   private String name;

   /**
    * The control ID.
    */
   private String controlId;
   
   /**
    * Default constructor.
    */
   public MemoryConnectionSetting() {
   }
   
   /**
    * Constructor.
    * @param key The key.
    * @param name The name.
    * @param controlId The control ID.
    */
   public MemoryConnectionSetting(String key, String name, String controlId) {
      super();
      this.key = key;
      this.name = name;
      this.controlId = controlId;
   }

   /**
    * Sets the key.
    * @param key The key to set.
    */
   public void setKey(String key) {
      this.key = key;
   }

   /**
    * Sets the name.
    * @param name The name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * Sets the control id.
    * @param controlId The id to set.
    */
   public void setControlId(String controlId) {
      this.controlId = controlId;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getKey() {
      return key;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getControlId() {
      return controlId;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getInitialValue(ISelection selection) {
      return null;
   }
}