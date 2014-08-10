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

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSProvable;

/**
 * Default implementation for an {@link IDSAttribute} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryAttribute extends AbstractDSProvable implements IDSAttribute {
   /**
    * The name.
    */
   private String name;
   
   /**
    * The type.
    */
   private String type;
   
   /**
    * The visibility.
    */
   private DSVisibility visibility;

   /**
    * Is static?
    */
   private boolean isStatic;
   
   /**
    * Is final?
    */
   private boolean isFinal;
   
   /**
    * All available obligations.
    */
   private List<String> obligations = new LinkedList<String>();
   
   /**
    * The parent.
    */
   private IDSType parent;
   
   /**
    * Default constructor.
    */
   public MemoryAttribute() {
   }
   
   /**
    * Constructor.
    * @param name The name.
    * @param type The type.
    * @param visibility The visibility.
    */
   public MemoryAttribute(String name, String type, DSVisibility visibility) {
      setName(name);
      setType(type);
      setVisibility(visibility);
   }
   
   /**
    * Constructor.
    * @param name The name.
    * @param type The type.
    * @param visibility The visibility.
    * @param isStatic Is static?
    */
   public MemoryAttribute(String name, 
                          String type, 
                          DSVisibility visibility, 
                          boolean isStatic) {
      setName(name);
      setType(type);
      setVisibility(visibility);
      setStatic(isStatic);
   }
   
   /**
    * Constructor.
    * @param name The name.
    * @param type The type.
    * @param visibility The visibility.
    * @param isStatic Is static?
    * @param isFinal Is final?
    */
   public MemoryAttribute(String name, 
                          String type, 
                          DSVisibility visibility, 
                          boolean isStatic, 
                          boolean isFinal) {
      setName(name);
      setType(type);
      setVisibility(visibility);
      setStatic(isStatic);
      setFinal(isFinal);
   }

   /**
    * Sets the name.
    * @param name The name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * Sets the type.
    * @param type The type to set.
    */
   public void setType(String type) {
      this.type = type;
   }

   /**
    * Sets the visibility.
    * @param visibility The visibility to set.
    */
   public void setVisibility(DSVisibility visibility) {
      this.visibility = visibility;
   }

   /**
    * Sets the static flag.
    * @param isStatic The flag to set.
    */
   public void setStatic(boolean isStatic) {
      this.isStatic = isStatic;
   }

   /**
    * Sets the final flag.
    * @param isFinal The final flag to set.
    */
   public void setFinal(boolean isFinal) {
      this.isFinal = isFinal;
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
   public String getType() {
      return type;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public DSVisibility getVisibility() {
      return visibility;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isStatic() {
      return isStatic;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isFinal() {
      return isFinal;
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
   public IDSType getParent() throws DSException {
      return parent;
   }

   /**
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSType parent) {
      this.parent = parent;
   }
}