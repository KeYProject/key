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

import java.util.LinkedList;
import java.util.List;

import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSContainer;

/**
 * Default implementation for an {@link IDSPackage} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryPackage extends AbstractDSContainer implements IDSPackage {
   /**
    * The name.
    */
   private String name;

   /**
    * The sub packages.
    */
   private List<IDSPackage> packages = new LinkedList<IDSPackage>();
   
   /**
    * The contained classes.
    */
   private List<IDSClass> classes = new LinkedList<IDSClass>();

   /**
    * The contained interfaces.
    */
   private List<IDSInterface> interfaces = new LinkedList<IDSInterface>();

   /**
    * The contained enumerations.
    */
   private List<IDSEnum> enums = new LinkedList<IDSEnum>();   

   /**
    * The parent {@link IDSContainer}.
    */
   private IDSContainer parent;
   
   /**
    * Default constructor.
    */
   public MemoryPackage() {
   }
   
   /**
    * Constructor.
    * @param name The name.
    */
   public MemoryPackage(String name) {
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
    * Sets the parent.
    * @param parent The parent to set.
    */
   public void setParent(IDSContainer parent) {
      this.parent = parent;
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
   public List<IDSPackage> getPackages() {
      return packages;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSClass> getClasses() {
      return classes;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSInterface> getInterfaces() {
      return interfaces;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSEnum> getEnums() {
      return enums;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSContainer getParent() throws DSException {
      return parent;
   }
   
   /**
    * Adds the child package and updates the parent reference on it.
    * @param child The new child package to add.
    */
   public void addPackage(MemoryPackage child) {
      getPackages().add(child);
      child.setParent(this);
   }
   
   /**
    * Adds the child class and updates the parent reference on it.
    * @param child The new child class to add.
    */
   public void addClass(MemoryClass child) {
      getClasses().add(child);
      child.setParentContainer(this);
   }
   
   /**
    * Adds the child interface and updates the parent reference on it.
    * @param child The new child interface to add.
    */
   public void addInterface(MemoryInterface child) {
      getInterfaces().add(child);
      child.setParentContainer(this);
   }
   
   /**
    * Adds the child enumeration and updates the parent reference on it.
    * @param child The new child enumeration to add.
    */
   public void addEnum(MemoryEnum child) {
      getEnums().add(child);
      child.setParentContainer(this);
   }
}