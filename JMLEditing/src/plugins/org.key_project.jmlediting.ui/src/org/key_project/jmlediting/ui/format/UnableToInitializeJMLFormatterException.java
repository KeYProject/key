package org.key_project.jmlediting.ui.format;

/**
 * An exception to signal that the {@link JMLContentFormatter} could not be
 * initialized.
 *
 * @author Moritz Lichter
 *
 */
public class UnableToInitializeJMLFormatterException extends Exception {

   /**
    *
    */
   private static final long serialVersionUID = 4108475852591697110L;

   /**
    * Creates a new exception instance.
    * 
    * @param message
    *           the message of the exception
    * @param cause
    *           another exception which caused this exception
    */
   public UnableToInitializeJMLFormatterException(final String message,
         final Throwable cause) {
      super(message, cause);
   }

}
