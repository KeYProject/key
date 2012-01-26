package org.key_project.swtbot.swing.util;

/**
 * A {@link Runnable} that returns some result.
 * @author Martin Hentschel
 */
public interface IRunnableWithResult<T> extends Runnable {
    /**
     * Return the result.
     * @return The result.
     */
    public T getResult();
}
