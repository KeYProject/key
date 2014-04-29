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

import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSProvable;

/**
 * Default implementation for an {@link IDSEnumLiteral} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryEnumLiteral extends AbstractDSProvable implements IDSEnumLiteral {
   /**
    * The name.
    */
   private String name;
   
   /**
    * All available obligations.
    */
   private List<String> obligations = new LinkedList<String>();
   
   /**
    * The parent {@link IDSEnum}.
    */
   private IDSEnum parent;

   /**
    * Default constructor.
    */
   public MemoryEnumLiteral() {
   }

   /**
    * Constructor.
    * @param name The name to set.
    */
   public MemoryEnumLiteral(String name) {
      setName(name);
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
   public String getName() {
      return name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getObligations() throws DSException {
      return obligations;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSEnum getParent() {
      return parent;
   }

   /**
    * Sets the parent {@link IDSEnum}.
    * @param parent The parent {@link IDSEnum} to set.
    */
   public void setParent(IDSEnum parent) {
      this.parent = parent;
   }
}