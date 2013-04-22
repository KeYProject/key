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

package de.hentschel.visualdbc.datasource.model.exception;

/**
 * An {@link Exception} that is thrown from a data source.
 * @author Martin Hentschel
 */
public class DSException extends Exception {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 9156461756885911960L;

   /**
    * Default constructor.
    */
   public DSException() {
      super();
   }

   /**
    * Constructor
    * @param message The message.
    * @param exception The contained exception.
    */
   public DSException(String message, Throwable exception) {
      super(message, exception);
   }

   /**
    * Constructor
    * @param message The message.
    */
   public DSException(String message) {
      super(message);
   }

   /**
    * Constructor
    * @param exception The contained exception.
    */
   public DSException(Throwable exception) {
      super(exception);
   }
}