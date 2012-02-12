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
 * A {@link Runnable} that has a result that is accessible via {@link #getResult()}.
 * </p>
 * <p>
 * Concrete implementations should be subclasses of {@link AbstractRunnableWithResult}.
 * </p>
 * @author Martin Hentschel
 * @see AbstractRunnableWithResult
 */
public interface IRunnableWithResult<T> extends IRunnableWithException {
   /**
    * Returns the result.
    * @return The result.
    */
   public T getResult();
   
   /**
    * Returns an occurred exception.
    * @return An occurred exception.
    */
   public Exception getException();
}
