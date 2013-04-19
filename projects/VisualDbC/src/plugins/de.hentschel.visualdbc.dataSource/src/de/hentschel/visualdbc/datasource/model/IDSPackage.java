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

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Represents a package on the data source.
 * @author Martin Hentschel
 */
public interface IDSPackage extends IDSContainer {
   /**
    * Returns the parent {@link IDSPackage} or {@link IDSConnection}.
    * @return The parent or {@code null} if it has no one.
    * @throws DSException Occurred Exception
    */
   public IDSContainer getParent() throws DSException;
   
   /**
    * Returns the package name.
    * @return The name.
    * @throws DSException Occurred Exception
    */
   public String getName() throws DSException;
}