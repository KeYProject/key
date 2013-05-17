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

package org.key_project.swtbot.swing.util;

/**
 * Provides a basic functionality of {@link IRunnableWithResult}.
 * @author Martin Hentschel
 */
public abstract class AbstractRunnableWithResultAndException<T> extends AbstractRunnableWithResult<T> implements IRunnableWithResultAndException<T> {
    /**
     * The occurred {@link Exception}.
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
     * Sets the occurred {@link Exception}.
     * @param exception The occurred {@link Exception} to set.
     */
    public void setException(Exception exception) {
        this.exception = exception;
    }
}