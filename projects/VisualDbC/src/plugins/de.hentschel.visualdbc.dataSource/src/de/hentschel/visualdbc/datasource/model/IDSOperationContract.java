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

package de.hentschel.visualdbc.datasource.model;

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Represents an operation contract on the data source.
 * @author Martin Hentschel
 */
public interface IDSOperationContract extends IDSSpecification {
   /**
    * Returns the pre conditions.
    * @return The pre conditions.
    * @throws DSException Occurred Exception
    */
   public String getPre() throws DSException;
   
   /**
    * Returns the post conditions.
    * @return The post conditions.
    * @throws DSException Occurred Exception
    */
   public String getPost() throws DSException;
   
   /**
    * Returns the modifies.
    * @return The modifies.
    * @throws DSException Occurred Exception
    */
   public String getModifies() throws DSException;
   
   /**
    * Returns the termination.
    * @return The termination.
    * @throws DSException Occurred Exception
    */
   public String getTermination() throws DSException;
   
   /**
    * Returns the parent {@link IDSOperation}.
    * @return The parent {@link IDSOperation}.
    * @throws DSException Occurred Exception
    */
   public IDSOperation getParent() throws DSException;
}