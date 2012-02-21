package org.key_project.util.java.thread;

/**
 * <p>
 * Provides a basic implementation of {@link IRunnableWithResult}.
 * </p>
 * <p>
 * The concrete implementations have to set the result 
 * via {@link #setResult(Object)} in {@link #run()}.
 * </p>
 * @author Martin Hentschel
 * @see IRunnableWithResult
 */
public abstract class AbstractRunnableWithResult<T> extends AbstractRunnableWithException implements IRunnableWithResult<T> {
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
   protected void setResult(T result) {
      this.result = result;
   }
}
