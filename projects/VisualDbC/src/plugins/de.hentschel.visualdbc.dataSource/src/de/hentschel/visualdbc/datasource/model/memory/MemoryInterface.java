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
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSMethod;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Default implementation for an {@link IDSInterface} for objects in the
 * memory.
 * @author Martin Hentschel
 */
public class MemoryInterface extends AbstractMemoryType implements IDSInterface {
   /**
    * The contained methods.
    */
   private List<IDSMethod> methods = new LinkedList<IDSMethod>();

   /**
    * The available extends references.
    */
   private List<IDSInterface> extendsReferences = new LinkedList<IDSInterface>();
   
   /**
    * The full names of all parents.
    */
   private List<String> extendsFullNames = new LinkedList<String>();
   
   /**
    * Default constructor.
    */
   public MemoryInterface() {
   }

   /**
    * Constructor
    * @param name The name.
    */
   public MemoryInterface(String name) {
      setName(name);
   }

   /**
    * Constructor.
    * @param name The name.
    * @param visibility The visibility.
    */
   public MemoryInterface(String name, DSVisibility visibility) {
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
   public List<IDSInterface> getExtends() {
      return extendsReferences ;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public List<String> getExtendsFullnames() {
      return extendsFullNames;
   }
   
   /**
    * Adds the method and updates his parent reference.
    * @param method The method to add.
    */
   public void addMethod(MemoryMethod method) {
      methods.add(method);
      method.setParent(this);
   }
}