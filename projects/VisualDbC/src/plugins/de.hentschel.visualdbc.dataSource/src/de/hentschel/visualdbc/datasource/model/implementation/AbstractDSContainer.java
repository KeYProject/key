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

package de.hentschel.visualdbc.datasource.model.implementation;

import java.util.Iterator;

import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSContainer;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSPackage;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Provides a basic implementation of {@link IDSContainer}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSContainer implements IDSContainer {
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSEnum getEnum(String name) throws DSException {
      Iterator<IDSEnum> iter = getEnums().iterator();
      IDSEnum result = null;
      while(result == null && iter.hasNext()) {
         IDSEnum next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSInterface getInterface(String name) throws DSException {
      Iterator<IDSInterface> iter = getInterfaces().iterator();
      IDSInterface result = null;
      while(result == null && iter.hasNext()) {
         IDSInterface next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSClass getClass(String name) throws DSException {
      Iterator<IDSClass> iter = getClasses().iterator();
      IDSClass result = null;
      while(result == null && iter.hasNext()) {
         IDSClass next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IDSPackage getPackage(String name) throws DSException {
      Iterator<IDSPackage> iter = getPackages().iterator();
      IDSPackage result = null;
      while(result == null && iter.hasNext()) {
         IDSPackage next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }
}