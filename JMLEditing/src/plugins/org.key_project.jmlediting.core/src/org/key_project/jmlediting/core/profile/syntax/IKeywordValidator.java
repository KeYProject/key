package org.key_project.jmlediting.core.profile.syntax;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;

/**
 * Class for Validating JML.
 *
 * @author David Giessing
 *
 */
public interface IKeywordValidator {

   /**
    * Method for checking if a given JMLComments Specifications (Represented by
    * a node) are valid.
    *
    * @param c
    *           the JMLComment to Validate in
    * @param context
    *           the context to validate in
    * @param node
    *           the node to validate
    *
    * @return a List of IMarkers if some Specifications are invalid or an empty
    *         list if they are all valid
    */
   List<JMLError> validate(CommentRange c, final IJMLValidationContext context,
         final IASTNode node);

   /**
    * Checks if node is a valid Statement for this Validator.
    *
    * @param node
    *           the Node to Validate
    * @return true if valid, else false
    */
   boolean isFollowingJavaElementValid(ASTNode node);
}