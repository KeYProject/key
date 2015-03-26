package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.EnhancedForStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordValidator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.ErrorTypes;
import org.key_project.jmlediting.core.utilities.JMLError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;

/**
 * This Class checks if Loop Invariant specifications in JML are placed valid,
 * which means that they are immediately followed by a loop in Java Code. It is
 * allowed to have another invariant between the invariant and the loop, but not
 * any other java or jml. Comments are allowed too.
 *
 * @author David Giessing
 *
 */
public class LoopInvariantValidator extends AbstractKeywordValidator {

   @Override
   public List<JMLError> validate(final CommentRange c,
         final IJMLValidationContext context, final IASTNode node) {
      final List<JMLError> errors = new ArrayList<JMLError>();
      // Validate the Loop Keyword
      if (!this.isFollowingJavaElementValid(context
            .getNodeForLeadingComment(context.getCommentForJMLComment(c)))) {
         errors.add(new JMLError("LoopValidationError",
               ErrorTypes.ValidationError, "Loop Specification followed"
                     + " by a non Loop Java Statement", node.getEndOffset()));
      }

      return errors;
   }

   @Override
   public boolean isFollowingJavaElementValid(final ASTNode node) {
      return (node instanceof ForStatement) || (node instanceof WhileStatement)
            || (node instanceof DoStatement)
            || (node instanceof EnhancedForStatement);
   }
}
