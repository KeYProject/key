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
 * Contains the available visibilities.
 * @author Martin Hentschel
 */
public enum DSVisibility {
   /**
    * Default.
    */
   DEFAULT,
   
   /**
    * Private.
    */
   PRIVATE,
   
   /**
    * Protected.
    */
   PROTECTED,
   
   /**
    * Public.
    */
   PUBLIC;
}
