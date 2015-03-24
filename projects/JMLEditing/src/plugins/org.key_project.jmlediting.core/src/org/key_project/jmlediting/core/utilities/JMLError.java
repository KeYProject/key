package org.key_project.jmlediting.core.utilities;

/**
 * Container class for ValidationErrors.
 *
 * @author David Giessing
 *
 */
public class JMLError {

   /**
    * Represents the errorType.
    */
   private final ErrorTypes errorType;
   /**
    * represents the errorMessage.
    */
   private final String errorMessage;
   /**
    * represents the offset of the Error.
    */
   private final int offset;

   /**
    * creates a new JMLValidationError.
    *
    * @param errorType
    *           the ErrorType
    * @param errorMessage
    *           the ErrorMessage
    * @param offset
    *           the offset of the Error
    */
   public JMLError(final ErrorTypes errorType, final String errorMessage,
         final int offset) {
      this.errorType = errorType;
      this.errorMessage = errorMessage;
      this.offset = offset;
   }

   /**
    * @return the errorType
    */
   public ErrorTypes getErrorType() {
      return this.errorType;
   }

   /**
    * @return the errorMessage
    */
   public String getErrorMessage() {
      return this.errorMessage;
   }

   /**
    * @return the invalidSpec
    */
   public int getOffset() {
      return this.offset;
   }
}
