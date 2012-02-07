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

/**
 * Represents a reference from an {@link IDSProvable} to another {@link IDSProvable}.
 * @author Martin Hentschel
 */
public interface IDSProvableReference {
   /**
    * Returns the target {@link IDSProvable}.
    * @return The target {@link IDSProvable}.
    */
   public IDSProvable getTargetProvable();
   
   /**
    * Returns a human readable label.
    * @return The label.
    */
   public String getLabel();
}
