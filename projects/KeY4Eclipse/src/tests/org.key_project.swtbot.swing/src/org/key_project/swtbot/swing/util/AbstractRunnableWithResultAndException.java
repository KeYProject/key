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
