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

import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSInvariant} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryInvariant extends MemorySpecification implements IDSInvariant {
   /**
    * The text.
    */
   private String text;
   
   /**
    * The parent.
    */
   private IDSType parent;

   /**
    * Default constructor.
    */
   public MemoryInvariant() {
   }
   
   /**
    * Constructor.
    * @param name The name.
    * @param text The text.
    */
   public MemoryInvariant(String name, String text) {
      setName(name);
      setText(text);
   }

   /**
    * Sets the text.
    * @param text The text to set.
    */
   public void setText(String text) {
      this.text = text;
   }

   /**
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSType parent) {
      this.parent = parent;
   }   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getCondition() throws DSException {
      return text;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSType getParent() throws DSException {
      return parent;
   }
}