/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java.thread;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * <p>
 * A {@link Runnable} that has a result that is accessible via {@link #getResult()}.
 * </p>
 * <p>
 * Concrete implementations should be subclasses of {@link AbstractRunnableWithResult}.
 * </p>
 *
 * @author Martin Hentschel
 * @see AbstractRunnableWithResult
 */
@NullMarked
public interface IRunnableWithResult<T> extends IRunnableWithException {
    /**
     * Returns the result.
     *
     * @return The result.
     */
    @Nullable
    T getResult();

    /**
     * Returns an occurred exception.
     *
     * @return An occurred exception.
     */
    @Nullable
    Exception getException();
}
