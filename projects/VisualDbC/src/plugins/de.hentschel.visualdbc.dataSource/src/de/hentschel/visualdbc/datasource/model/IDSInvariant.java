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
 * Represents an invariant on the data source.
 * @author Martin Hentschel
 */
public interface IDSInvariant extends IDSSpecification {
   /**
    * Returns the text.
    * @return The text.
    * @throws DSException Occurred Exception
    */
   public String getCondition() throws DSException;
   
   /**
    * Returns the parent {@link IDSType}.
    * @return The parent {@link IDSType}.
    * @throws DSException Occurred Exception
    */
   public IDSType getParent() throws DSException;
}
