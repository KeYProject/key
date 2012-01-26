package org.key_project.swtbot.swing.util;

/**
 * A {@link Runnable} that returns some result.
 * @author Martin Hentschel
 */
public interface IRunnableWithResultAndException<T> extends IRunnableWithResult<T> {
    /**
     * Return the occurred {@link Exception}.
     * @return The occurred {@link Exception}.
     */
    public Exception getException();
}
