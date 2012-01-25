/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.datasource.model.memory;

import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;

/**
 * Default implementation for an {@link IDSEnumLiteral} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryEnumLiteral implements IDSEnumLiteral {
   /**
    * The name.
    */
   private String name;
   
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
   public String getName() {
      return name;
   }
}
