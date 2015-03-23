package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;
import org.key_project.jmlediting.core.validation.IKeywordValidator;

/**
 * This Class checks if Loop Invariant specifications in JML are placed valid,
 * which means that they are immediately followed by a loop in Java Code. It is
 * allowed to have another invariant between the invariant and the loop, but not
 * any other java or jml. Comments are allowed too.
 *
 * @author David Giessing
 *
 */
public class LoopInvariantValidator extends IKeywordValidator {

   @Override
   public List<JMLValidationError> validate(final CommentRange c,
         final IJMLValidationContext context, final IASTNode node) {
      final List<JMLValidationError> errors = new ArrayList<JMLValidationError>();
      // Validate the Loop Keyword
      if (!isLoop(context.getNodeForLeadingComment(context
            .getCommentForJMLComment(c)))) {
         // TODO do not encode marker ID here
         errors.add(new JMLValidationError(
               "org.key_project.jmlediting.core.validationerror",
               "Loop Specification followed by a non Loop Java Statement", node));
      }

      return errors;
   }

   public static boolean isLoop(final ASTNode node) {
      return (node instanceof ForStatement) || (node instanceof WhileStatement)
            || (node instanceof DoStatement);
   }
}
