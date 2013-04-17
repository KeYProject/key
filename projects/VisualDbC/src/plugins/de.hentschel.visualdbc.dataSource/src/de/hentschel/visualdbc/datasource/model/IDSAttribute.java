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
 * Represents an attribute on the data source.
 * @author Martin Hentschel
 */
public interface IDSAttribute extends IDSProvable {
   /**
    * Returns the parent.
    * @return The parent.
    * @throws DSException Occurred Exception
    */
   public IDSType getParent() throws DSException;
   
   /**
    * Returns the attribute name.
    * @return The attribute name.
    * @throws DSException Occurred Exception
    */
   public String getName() throws DSException;
   
   /**
    * Returns the type.
    * @return The type.
    * @throws DSException Occurred Exception
    */
   public String getType() throws DSException;
   
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
    * Checks if it is final.
    * @return Is final?
    * @throws DSException Occurred Exception
    */
   public boolean isFinal() throws DSException;
}