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

package de.hentschel.visualdbc.datasource.model;

import de.hentschel.visualdbc.datasource.model.exception.DSException;

/**
 * Represents an enumeration literal on the data source.
 * @author Martin Hentschel
 */
public interface IDSEnumLiteral {
   /**
    * Returns the enumeration literal name.
    * @return The enumeration literal name.
    * @throws DSException Occurred Exception
    */
   public String getName() throws DSException;
}
