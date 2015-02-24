package org.key_project.jmlediting.core.utilities;

import org.key_project.jmlediting.core.dom.IASTNode;

/**
 * Container class for ValidationErrors.
 *
 * @author David Giessing
 *
 */
public class JMLValidationError {

   /**
    * Represents the errorType.
    */
   private final String errorType;
   /**
    * represents the errorMessage.
    */
   private final String errorMessage;
   /**
    * represents the Invalid Node.
    */
   private final IASTNode invalidSpec;

   /**
    * creates a new JMLValidationError.
    *
    * @param errorType
    *           the ErrorType
    * @param errorMessage
    *           the ErrorMessage
    * @param invalidSpec
    *           the Invalid JML Node
    */
   public JMLValidationError(final String errorType, final String errorMessage,
         final IASTNode invalidSpec) {
      this.errorType = errorType;
      this.errorMessage = errorMessage;
      this.invalidSpec = invalidSpec;
   }

   /**
    * @return the errorType
    */
   public String getErrorType() {
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
   public IASTNode getInvalidSpec() {
      return this.invalidSpec;
   }
}
