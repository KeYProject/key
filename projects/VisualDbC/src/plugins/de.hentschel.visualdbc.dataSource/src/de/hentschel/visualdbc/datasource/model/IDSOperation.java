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

package de.hentschel.visualdbc.datasource.model;

import java.util.List;

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Provides a basic implementation for an operation like
 * {@link IDSMethod}s or {@link IDSConstructor}s.
 * @author Martin Hentschel
 */
public interface IDSOperation extends IDSProvable {
   /**
    * Returns the method signature.
    * @return The method signature.
    * @throws DSException Occurred Exception
    */
   public String getSignature() throws DSException;
   
   /**
    * Returns the visibility.
    * @return The visibility.
    * @throws DSException Occurred Exception
    */
   public DSVisibility getVisibility() throws DSException;
   
   /**
    * Checks if it is static.
    * @return Is static?
    * @throws DSException Occurred Exception
    */
   public boolean isStatic() throws DSException;
   
   /**
    * Returns all operation contracts.
    * @return The operation contracts.
    * @throws DSException Occurred Exception
    */
   public List<IDSOperationContract> getOperationContracts() throws DSException;

   /**
    * Returns the operation contract with the given pre and post condition.
    * @param pre The pre condition.
    * @param post The post condition.
    * @return The found {@link IDSOperationContract} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSOperationContract getOperationContract(String pre, String post) throws DSException;
   
   /**
    * Returns the parent.
    * @return The parent.
    */
   public IDSType getParent();
}