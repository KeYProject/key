package org.key_project.util.java.thread;

/**
 * Provides a basic implementation of {@link IRunnableWithProgressAndResult}.
 * @author Martin Hentschel
 */
public abstract class AbstractRunnableWithProgressAndResult<T> implements IRunnableWithProgressAndResult<T> {
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
     * @param result The result to ste.
     */
    protected void setResult(T result) {
        this.result = result;
    }
}
