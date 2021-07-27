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

package org.key_project.util.java.thread;

/**
 * <p>
 * Provides a basic implementation of {@link IRunnableWithException}.
 * </p>
 * <p>
 * The concrete implementations have to set the exception 
 * via {@link #setException(Exception)} in {@link #run()}.
 * </p>
 * @author Martin Hentschel
 * @see IRunnableWithResult
 */
public abstract class AbstractRunnableWithException implements IRunnableWithException {
   /**
    * An occurred exception.
    */
   private Exception exception;
   
   /**
    * {@inheritDoc}
    */
   @Override   
   public Exception getException() {
      return exception;
   }

   /**
    * Sets the occurred exception.
    * @param exception The occurred exception.
    */
   protected void setException(Exception exception) {
      this.exception = exception;
   }
}