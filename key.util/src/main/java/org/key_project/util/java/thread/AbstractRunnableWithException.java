/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java.thread;

/**
 * <p>
 * Provides a basic implementation of {@link IRunnableWithException}.
 * </p>
 * <p>
 * The concrete implementations have to set the exception via {@link #setException(Exception)} in
 * {@link #run()}.
 * </p>
 *
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
     *
     * @param exception The occurred exception.
     */
    protected void setException(Exception exception) {
        this.exception = exception;
    }
}
