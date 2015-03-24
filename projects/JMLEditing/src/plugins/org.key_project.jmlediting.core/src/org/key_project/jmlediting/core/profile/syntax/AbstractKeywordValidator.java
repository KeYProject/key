package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;

/**
 * Superclass for Keyword Validators. Subclasses have to call the Constructor,
 * to set its SpecificErrorType (e.g.LoopValidationError)
 * 
 * @author David Giessing
 *
 */
public abstract class AbstractKeywordValidator implements IKeywordValidator {

   /**
    * The specificErrorType for this Validator.
    */
   private final String specificErrorType;

   /**
    * Generates an AbstractKeywordValidator with specific ErrorType type.
    *
    * @param errorType
    *           the specific ErrorType
    */
   public AbstractKeywordValidator(final String errorType) {
      this.specificErrorType = errorType;
   }

   @Override
   public abstract List<JMLError> validate(CommentRange c,
         IJMLValidationContext context, IASTNode node);

   @Override
   public String generateErrorMessage(final String errorMessage) {
      return this.specificErrorType + errorMessage;
   }
}
