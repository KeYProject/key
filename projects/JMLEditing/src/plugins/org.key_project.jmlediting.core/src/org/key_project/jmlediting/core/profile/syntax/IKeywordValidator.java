package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;

/**
 * Class for Validating JML.
 *
 * @author David Giessing
 *
 */
public interface IKeywordValidator extends IJMLValidator {

   /*
    * (non-Javadoc)
    * 
    * @see
    * org.key_project.jmlediting.core.validator.JMLValidator#isValid(org.key_project
    * .jmlediting.core.dom.IASTNode)
    */
   @Override
   public abstract List<JMLValidationError> validate(CommentRange c,
         final IJMLValidationContext context, final IASTNode node);
}