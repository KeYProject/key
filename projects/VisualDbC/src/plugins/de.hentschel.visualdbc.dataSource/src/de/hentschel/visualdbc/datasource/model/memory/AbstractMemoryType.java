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

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.model.DSVisibility;
import de.hentschel.visualdbc.datasource.model.IDSAttribute;
import de.hentschel.visualdbc.datasource.model.IDSAxiom;
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSInvariant;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;
import de.hentschel.visualdbc.datasource.model.implementation.AbstractDSType;

/**
 * Default implementation for an {@link IDSType} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public abstract class AbstractMemoryType extends AbstractDSType {
   /**
    * The name.
    */
   private String name;
   
   /**
    * The visibility.
    */
   private DSVisibility visibility;
   
   /**
    * Static?
    */
   private boolean isStatic;

   /**
    * The contained inner classes.
    */
   private List<IDSClass> innerClasses = new LinkedList<IDSClass>();

   /**
    * The contained inner interfaces.
    */
   private List<IDSInterface> innerInterfaces = new LinkedList<IDSInterface>();

   /**
    * The contained inner enumerations.
    */
   private List<IDSEnum> innerEnums = new LinkedList<IDSEnum>();

   /**
    * All available obligations.
    */
   private List<String> obligations = new LinkedList<String>();
   
   /**
    * The parent container.
    */
   private IDSContainer parentContainer;
   
   /**
    * The parent type.
    */
   private IDSType parentType;
   
   /**
    * Contains all invariants.
    */
   private List<IDSInvariant> invariants = new LinkedList<IDSInvariant>();
   
   /**
    * Contains all axioms.
    */
   private List<IDSAxiom> axioms = new LinkedList<IDSAxiom>();

   /**
    * The contained attributes.
    */
   private List<IDSAttribute> attributes = new LinkedList<IDSAttribute>();
      
   /**
    * Sets the parent package.
    * @param parentContainer The parent package to set.
    */
   public void setParentContainer(IDSContainer parentContainer) {
      this.parentContainer = parentContainer;
   }

   /**
    * Sets the parent type.
    * @param parentType The parent type to set.
    */
   public void setParentType(IDSType parentType) {
      this.parentType = parentType;
   }

   /**
    * Sets the name.
    * @param name The name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * Sets te visibility.
    * @param visibility The visibility to set.
    */
   public void setVisibility(DSVisibility visibility) {
      this.visibility = visibility;
   }

   /**
    * Sets the static flag.
    * @param isStatic The static flag to set.
    */
   public void setStatic(boolean isStatic) {
      this.isStatic = isStatic;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSAttribute> getAttributes() {
      return attributes;
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
   public List<IDSClass> getInnerClasses() {
      return innerClasses;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSInterface> getInnerInterfaces() {
      return innerInterfaces;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSEnum> getInnerEnums() {
      return innerEnums ;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getObligations() {
      return obligations;
   }   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSContainer getParentContainer() {
      return parentContainer;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSType getParentType() {
      return parentType;
   }
   
   /**
    * Adds the inner class.
    * @param classInstance The inner class to add.
    */
   public void addInnerClass(MemoryClass classInstance) {
      getInnerClasses().add(classInstance);
      classInstance.setParentType(this);
   }
   
   /**
    * Adds the inner interface.
    * @param interfaceInstance The inner interface to add.
    */
   public void addInnerInterface(MemoryInterface interfaceInstance) {
      getInnerInterfaces().add(interfaceInstance);
      interfaceInstance.setParentType(this);
   }
   
   /**
    * Adds the inner enumeration.
    * @param enumInstance The inner enumeration to add.
    */
   public void addInnerEnum(MemoryEnum enumInstance) {
      getInnerEnums().add(enumInstance);
      enumInstance.setParentType(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSInvariant> getInvariants() {
      return invariants;
   }
   
   /**
    * Adds the invariant and updates his parent reference.
    * @param invariant The invariant to add.
    */
   public void addInvariant(MemoryInvariant invariant) {
      invariants.add(invariant);
      invariant.setParent(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSAxiom> getAxioms() {
      return axioms;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAxiom getAxiom(String definition) throws DSException {
      Iterator<IDSAxiom> iter = getAxioms().iterator();
      IDSAxiom result = null;
      while(result == null && iter.hasNext()) {
         IDSAxiom next = iter.next();
         if (next != null && ObjectUtil.equals(next.getDefinition(), definition)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSInvariant getInvariant(String condition) throws DSException {
      Iterator<IDSInvariant> iter = getInvariants().iterator();
      IDSInvariant result = null;
      while(result == null && iter.hasNext()) {
         IDSInvariant next = iter.next();
         if (next != null && ObjectUtil.equals(next.getCondition(), condition)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSAttribute getAttribute(String name) throws DSException {
      Iterator<IDSAttribute> iter = getAttributes().iterator();
      IDSAttribute result = null;
      while(result == null && iter.hasNext()) {
         IDSAttribute next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }
   
   /**
    * Adds the axiom and updates his parent reference.
    * @param axiom The axiom to add.
    */
   public void addAxiom(MemoryAxiom axiom) {
      axioms.add(axiom);
      axiom.setParent(this);
   }
   
   /**
    * Adds the attribute and updates his parent reference.
    * @param attribute The attribute to add.
    */
   public void addAttribute(MemoryAttribute attribute) {
      attributes.add(attribute);
      attribute.setParent(this);
   }
}