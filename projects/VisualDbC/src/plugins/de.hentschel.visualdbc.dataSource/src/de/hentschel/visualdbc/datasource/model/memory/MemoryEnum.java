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
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSEnumLiteral;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSEnum} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryEnum extends AbstractMemoryType implements IDSEnum {
   /**
    * The contained methods.
    */
   private List<IDSMethod> methods = new LinkedList<IDSMethod>();

   /**
    * The contained constructors.
    */
   private List<IDSConstructor> constructors = new LinkedList<IDSConstructor>();

   /**
    * The contained literals.
    */
   private List<IDSEnumLiteral> literals = new LinkedList<IDSEnumLiteral>();

   /**
    * The available implements references.
    */
   private List<IDSInterface> implementsReferences = new LinkedList<IDSInterface>();

   /**
    * The full name of all realized interfaces.
    */
   private List<String> implementsFullNames = new LinkedList<String>();
   
   /**
    * Default constructor.
    */
   public MemoryEnum() {
   }

   /**
    * Constructor
    * @param name The name.
    */
   public MemoryEnum(String name) {
      setName(name);
   }

   /**
    * Constructor.
    * @param name The name.
    * @param visibility The visibility.
    */
   public MemoryEnum(String name, DSVisibility visibility) {
      setName(name);
      setVisibility(visibility);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSMethod> getMethods() {
      return methods;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSMethod getMethod(String signature) throws DSException {
      Iterator<IDSMethod> iter = getMethods().iterator();
      IDSMethod result = null;
      while(result == null && iter.hasNext()) {
         IDSMethod next = iter.next();
         if (next != null && ObjectUtil.equals(next.getSignature(), signature)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */   
   @Override
   public IDSConstructor getConstructor(String signature) throws DSException {
      Iterator<IDSConstructor> iter = getConstructors().iterator();
      IDSConstructor result = null;
      while(result == null && iter.hasNext()) {
         IDSConstructor next = iter.next();
         if (next != null && ObjectUtil.equals(next.getSignature(), signature)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSConstructor> getConstructors() {
      return constructors ;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSEnumLiteral> getLiterals() {
      return literals;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSInterface> getImplements() {
      return implementsReferences;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getImplementsFullnames() {
      return implementsFullNames;
   }
   
   /**
    * Adds the method and updates his parent reference.
    * @param method The method to add.
    */
   public void addMethod(MemoryMethod method) {
      methods.add(method);
      method.setParent(this);
   }
   
   /**
    * Adds the literal and updates his parent reference.
    * @param literal The literal to add.
    */
   public void addLiteral(MemoryEnumLiteral literal) {
      literals.add(literal);
      literal.setParent(this);
   }
   
   /**
    * Adds the constructor and updates his parent reference.
    * @param constructor The constructor to add.
    */
   public void addConstructor(MemoryConstructor constructor) {
      constructors.add(constructor);
      constructor.setParent(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSEnumLiteral getLiteral(String name) throws DSException {
      Iterator<IDSEnumLiteral> iter = getLiterals().iterator();
      IDSEnumLiteral result = null;
      while(result == null && iter.hasNext()) {
         IDSEnumLiteral next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }
}