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

package org.key_project.key4eclipse.util.java.thread;

/**
 * <p>
 * Provides a basic implementation of {@link IRunnableWithResult}.
 * </p>
 * <p>
 * The concrete implementations have to set the result 
 * via {@link #setResult(Object)} in {@link #run()}.
 * </p>
 * @author Martin Hentschel
 * @see IRunnableWithResult
 */
public abstract class AbstractRunnableWithResult<T> implements IRunnableWithResult<T> {
   /**
    * The result.
    */
   private T result;
   
   /**
    * An occurred exception.
    */
   private Exception exception;

   /**
    * {@inheritDoc}
    */
   @Override
   public T getResult() {
      return result;
   }

   /**
    * Sets the result.
    * @param result The result to set.
    */
   protected void setResult(T result) {
      this.result = result;
   }
   
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
