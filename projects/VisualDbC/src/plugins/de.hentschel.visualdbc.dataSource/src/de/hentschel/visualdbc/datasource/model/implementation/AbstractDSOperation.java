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

import org.key_project.util.java.ObjectUtil;

import de.hentschel.visualdbc.datasource.model.IDSOperation;
import de.hentschel.visualdbc.datasource.model.IDSOperationContract;
import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Provides a basic implementation of {@link IDSOperation}.
 * @author Martin Hentschel
 */
public abstract class AbstractDSOperation extends AbstractDSProvable implements IDSOperation {
   /**
    * {@inheritDoc}
    */
   @Override
   public IDSOperationContract getOperationContract(String pre, String post) throws DSException {
      Iterator<IDSOperationContract> iter = getOperationContracts().iterator();
      IDSOperationContract result = null;
      while(result == null && iter.hasNext()) {
         IDSOperationContract next = iter.next();
         if (next != null && 
             ObjectUtil.equals(next.getPre(), pre) &&
             ObjectUtil.equals(next.getPost(), post)) {
            result = next;
         }
      }
      return result;
   }
}
