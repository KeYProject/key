/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.util.java.thread;

import org.jspecify.annotations.Nullable;

/**
 * <p>
 * A {@link Runnable} that provides access to an exception that occurred during execution
 * {@link #getException()}.
 * </p>
 * <p>
 * Concrete implementations should be subclasses of {@link AbstractRunnableWithException}.
 * </p>
 *
 * @author Martin Hentschel
 * @see AbstractRunnableWithException
 */
public interface IRunnableWithException extends Runnable {
    /**
     * Returns an occurred exception.
     *
     * @return An occurred exception.
     */
    @Nullable
    Exception getException();
}
