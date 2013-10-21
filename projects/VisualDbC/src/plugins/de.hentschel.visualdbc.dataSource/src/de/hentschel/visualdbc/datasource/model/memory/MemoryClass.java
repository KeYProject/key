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
import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSConstructor;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSConnection} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryClass extends AbstractMemoryType implements IDSClass {
   /**
    * Final?
    */
   private boolean isFinal;
   
   /**
    * Abstract?
    */
   private boolean isAbstract;

   /**
    * Anonymous?
    */
   private boolean anonymous;
   
   /**
    * The contained methods.
    */
   private List<IDSMethod> methods = new LinkedList<IDSMethod>();

   /**
    * The contained constructors.
    */
   private List<IDSConstructor> constructors = new LinkedList<IDSConstructor>();

   /**
    * The available extends references.
    */
   private List<IDSClass> extendsReferences = new LinkedList<IDSClass>();

   /**
    * The available implements references.
    */
   private List<IDSInterface> implementsReferences = new LinkedList<IDSInterface>();
   
   /**
    * The full names of all parents.
    */
   private List<String> extendsFullNames = new LinkedList<String>();
   
   /**
    * The full name of all realized interfaces.
    */
   private List<String> implementsFullNames = new LinkedList<String>();
   
   /**
    * Default constructor.
    */
   public MemoryClass() {
   }

   /**
    * Constructor.
    * @param name The name.
    */
   public MemoryClass(String name) {
      setName(name);
   }

   /**
    * Constructor.
    * @param name The name.
    * @param visibility The visibility.
    */
   public MemoryClass(String name, DSVisibility visibility) {
      setName(name);
      setVisibility(visibility);
   }

   /**
    * Constructor.
    * @param name The name.
    * @param visibility The visibility.
    * @param isAbstract Abstract?
    */
   public MemoryClass(String name, 
                      DSVisibility visibility, 
                      boolean isAbstract) {
      setName(name);
      setVisibility(visibility);
      setAbstract(isAbstract);
   }

   /**
    * Constructor.
    * @param name The name.
    * @param visibility The visibility.
    * @param isAbstract Abstract?
    * @param isFinal Final?
    */
   public MemoryClass(String name, 
                      DSVisibility visibility, 
                      boolean isAbstract, 
                      boolean isFinal) {
      setName(name);
      setVisibility(visibility);
      setAbstract(isAbstract);
      setFinal(isFinal);
   }

   /**
    * Sets the final flag.
    * @param isFinal The final flag to set.
    */
   public void setFinal(boolean isFinal) {
      this.isFinal = isFinal;
   }

   /**
    * Sets the abstract flag.
    * @param isAbstract The abstract flag to set.
    */
   public void setAbstract(boolean isAbstract) {
      this.isAbstract = isAbstract;
   }
   
   /**
    * Marks this class as anonymous or not.
    * @param anonymous The anonymous flag to set.
    */
   public void setAnonymous(boolean anonymous) {
      this.anonymous = anonymous;
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
   public boolean isAbstract() {
      return isAbstract;
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
   public List<IDSConstructor> getConstructors() {
      return constructors ;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSClass> getExtends() {
      return extendsReferences ;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<IDSInterface> getImplements() {
      return implementsReferences ;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isAnonymous() {
      return anonymous;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getExtendsFullnames() {
      return extendsFullNames;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getImplementsFullnames() {
      return implementsFullNames;
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
    * Adds the method and updates his parent reference.
    * @param method The method to add.
    */
   public void addMethod(MemoryMethod method) {
      methods.add(method);
      method.setParent(this);
   }
   
   /**
    * Adds the constructor and updates his parent reference.
    * @param constructor The constructor to add.
    */
   public void addConstructor(MemoryConstructor constructor) {
      constructors.add(constructor);
      constructor.setParent(this);
   }
}