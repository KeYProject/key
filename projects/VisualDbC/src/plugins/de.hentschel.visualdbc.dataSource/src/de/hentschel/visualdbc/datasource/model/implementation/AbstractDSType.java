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

package de.hentschel.visualdbc.datasource.model.implementation;

import java.util.Iterator;

import org.key_project.key4eclipse.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.model.IDSClass;
import de.hentschel.visualdbc.datasource.model.IDSEnum;
import de.hentschel.visualdbc.datasource.model.IDSInterface;
import de.hentschel.visualdbc.datasource.model.IDSType;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Provides a basic implementation of {@link IDSType}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSType extends AbstractDSProvable implements IDSType {
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSEnum getInnerEnum(String name) throws DSException {
      Iterator<IDSEnum> iter = getInnerEnums().iterator();
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
   public IDSInterface getInnerInterface(String name) throws DSException {
      Iterator<IDSInterface> iter = getInnerInterfaces().iterator();
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
   public IDSClass getInnerClass(String name) throws DSException {
      Iterator<IDSClass> iter = getInnerClasses().iterator();
      IDSClass result = null;
      while(result == null && iter.hasNext()) {
         IDSClass next = iter.next();
         if (next != null && ObjectUtil.equals(next.getName(), name)) {
            result = next;
         }
      }
      return result;
   }
}
