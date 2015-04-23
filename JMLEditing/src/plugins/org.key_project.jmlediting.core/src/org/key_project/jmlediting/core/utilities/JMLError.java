package org.key_project.jmlediting.core.utilities;

/**
 * Container class for ValidationErrors.
 *
 * @author David Giessing
 *
 */
public class JMLError {

   /**
    * The Specific ErrorType of the JMLError. Used for Validators to differ
    * between different validation errors.
    */
   private final String specificErrorType;

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
    * @param specificError
    *           the specific error to differ between different validation errors
    *
    * @param errorType
    *           the ErrorType
    * @param errorMessage
    *           the ErrorMessage
    * @param offset
    *           the offset of the Error
    */
   public JMLError(final String specificError, final ErrorTypes errorType,
         final String errorMessage, final int offset) {
      this.specificErrorType = specificError;
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
      return this.specificErrorType + ": " + this.errorMessage;
   }

   /**
    * @return the invalidSpec
    */
   public int getOffset() {
      return this.offset;
   }
}
