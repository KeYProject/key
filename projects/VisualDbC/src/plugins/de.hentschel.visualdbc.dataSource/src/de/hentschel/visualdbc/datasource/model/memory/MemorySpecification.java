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

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSSpecification;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSProvable;

/**
 * Default implementation for an {@link IDSSpecification} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemorySpecification extends AbstractDSProvable implements IDSSpecification {
   /**
    * The name.
    */
   private String name;
   
   /**
    * All available obligations.
    */
   private List<String> obligations = new LinkedList<String>();

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return name;
   }

   /**
    * Sets the name.
    * @param name The name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getObligations() {
      return obligations;
   }
}