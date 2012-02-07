package org.key_project.key4eclipse.util.java.thread;

import org.eclipse.jface.operation.IRunnableWithProgress;

/**
 * Extended functionality of an {@link IRunnableWithProgress} that 
 * returns also one single result available via {@link #getResult()}.
 * @author Martin Hentschel
 */
public interface IRunnableWithProgressAndResult<T> extends IRunnableWithProgress {
    /**
     * Returns the result.
     * @return The single result.
     */
    public T getResult();
}
