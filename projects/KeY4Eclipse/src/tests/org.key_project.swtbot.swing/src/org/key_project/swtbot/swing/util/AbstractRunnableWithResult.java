package org.key_project.swtbot.swing.util;

/**
 * Provides a basic functionality of {@link IRunnableWithResult}.
 * @author Martin Hentschel
 */
public abstract class AbstractRunnableWithResult<T> implements IRunnableWithResult<T> {
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
    public void setResult(T result) {
        this.result = result;
    }
}
