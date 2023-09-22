/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java.thread;

/**
 * <p>
 * Provides a basic implementation of {@link IRunnableWithResult}.
 * </p>
 * <p>
 * The concrete implementations have to set the result via {@link #setResult(Object)} in
 * {@link #run()}.
 * </p>
 *
 * @author Martin Hentschel
 * @see IRunnableWithResult
 */
public abstract class AbstractRunnableWithResult<T> extends AbstractRunnableWithException
        implements IRunnableWithResult<T> {
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
     *
     * @param result The result to set.
     */
    protected void setResult(T result) {
        this.result = result;
    }
}
