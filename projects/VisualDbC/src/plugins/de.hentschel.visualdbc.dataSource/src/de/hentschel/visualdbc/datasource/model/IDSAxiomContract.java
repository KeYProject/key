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
public interface IDSAxiomContract extends IDSSpecification {
   /**
    * Returns the pre conditions.
    * @return The pre conditions.
    * @throws DSException Occurred Exception
    */
   public String getPre() throws DSException;
   
   /**
    * Returns the dep conditions.
    * @return The dep conditions.
    * @throws DSException Occurred Exception
    */
   public String getDep() throws DSException;
   
   /**
    * Returns the parent {@link IDSAxiom}.
    * @return The parent {@link IDSAxiom}.
    * @throws DSException Occurred Exception
    */
   public IDSAxiom getParent() throws DSException;
}