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
 * Represents an axiom on the data source.
 * @author Martin Hentschel
 */
public interface IDSAxiom extends IDSSpecification {
   /**
    * Returns the axiom definition.
    * @return The axiom definition.
    * @throws DSException Occurred Exception
    */
   public String getDefinition() throws DSException;
   
   /**
    * Returns the parent {@link IDSType}.
    * @return The parent {@link IDSType}.
    * @throws DSException Occurred Exception
    */
   public IDSType getParent() throws DSException;
   
   /**
    * Returns all operation contracts.
    * @return The operation contracts.
    * @throws DSException Occurred Exception
    */
   public List<IDSAxiomContract> getAxiomContracts() throws DSException;

   /**
    * Returns the operation contract with the given pre and dep condition.
    * @param pre The pre condition.
    * @param dep The dep condition.
    * @return The found {@link IDSAxiomContract} or {@code null} if no one was found.
    * @throws DSException Occurred Exception.
    */
   public IDSAxiomContract getAxiomContract(String pre, String dep) throws DSException;
}