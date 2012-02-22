package org.key_project.util.java.thread;

/**
 * <p>
 * A {@link Runnable} that has a result that is accessible via {@link #getResult()}.
 * </p>
 * <p>
 * Concrete implementations should be subclasses of {@link AbstractRunnableWithException}.
 * </p>
 * @author Martin Hentschel
 * @see AbstractRunnableWithException
 */
public interface IRunnableWithException extends Runnable {
   /**
    * Returns an occurred exception.
    * @return An occurred exception.
    */
   public Exception getException();
}
