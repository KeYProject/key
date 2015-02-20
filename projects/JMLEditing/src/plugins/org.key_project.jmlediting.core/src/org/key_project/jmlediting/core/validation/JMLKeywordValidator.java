package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.JMLValidationError;

/**
 * Class for Validating JML.
 *
 * @author David Giessing
 *
 */
public abstract class JMLKeywordValidator implements IJMLValidator {

   /*
    * (non-Javadoc)
    * 
    * @see
    * org.key_project.jmlediting.core.validator.JMLValidator#isValid(org.key_project
    * .jmlediting.core.dom.IASTNode)
    */
   @Override
   public abstract List<JMLValidationError> validate(
         final IJMLValidationContext context, final IASTNode node);
}