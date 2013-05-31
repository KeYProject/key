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

package org.key_project.util.java.thread;

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
public abstract class AbstractRunnableWithResult<T> extends AbstractRunnableWithException implements IRunnableWithResult<T> {
   /**
    * The result.
    */
   private T result;
   
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
}