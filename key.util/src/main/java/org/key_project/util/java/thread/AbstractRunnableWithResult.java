package org.key_project.util.java.thread;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

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
@NullMarked
public abstract class AbstractRunnableWithResult<T> extends AbstractRunnableWithException
        implements IRunnableWithResult<T> {
    /**
     * The result.
     */
    private @Nullable T result;

    /**
     * {@inheritDoc}
     */
    @Override
    public @Nullable T getResult() {
        return result;
    }

    /**
     * Sets the result.
     *
     * @param result The result to set.
     */
    protected void setResult(@Nullable T result) {
        this.result = result;
    }
}
