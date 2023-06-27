package org.key_project.util.java.thread;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * <p>
 * A {@link Runnable} that has a result that is accessible via {@link #getResult()}.
 * </p>
 * <p>
 * Concrete implementations should be subclasses of {@link AbstractRunnableWithException}.
 * </p>
 *
 * @author Martin Hentschel
 * @see AbstractRunnableWithException
 */
@NullMarked
public interface IRunnableWithException extends Runnable {
    /**
     * Returns an occurred exception.
     *
     * @return An occurred exception.
     */
    @Nullable Exception getException();
}
