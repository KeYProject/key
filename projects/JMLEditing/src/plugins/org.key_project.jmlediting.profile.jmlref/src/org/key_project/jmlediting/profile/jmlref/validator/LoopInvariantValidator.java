package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.DoStatement;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;
import org.key_project.jmlediting.core.validation.JMLKeywordValidator;
import org.key_project.jmlediting.profile.jmlref.loop.DecreasingKeyword;
import org.key_project.jmlediting.profile.jmlref.loop.LoopInvariantKeyword;

/**
 * This Class checks if Loop Invariant specifications in JML are placed valid,
 * which means that they are immediately followed by a loop in Java Code. It is
 * allowed to have another invariant between the invariant and the loop, but not
 * any other java or jml. Comments are allowed too.
 *
 * @author David Giessing
 *
 */
public class LoopInvariantValidator extends JMLKeywordValidator {

   /**
    * A List of LoopNodes in the JavaAST.
    */
   private final List<ASTNode> loopNodes = new ArrayList<ASTNode>();
   private final List<IKeywordNode> keywords = new ArrayList<IKeywordNode>();
   private CommentRange containingComment;

   @Override
   public List<JMLValidationError> validate(final CommentRange c,
         final IJMLValidationContext context, final IASTNode node) {
      final List<JMLValidationError> errors = new ArrayList();
      for (final IKeywordNode iKeywordNode : this.keywords) {
         if ((iKeywordNode.getKeyword() instanceof LoopInvariantKeyword)
               || (iKeywordNode.getKeyword() instanceof DecreasingKeyword)) {
            // Validate the Loop Keywords
            if (this.checkForLoop(context.getInverse().get(
                  context.getJmlCommentToInverse().get(c)))) {
               continue;
            }
            else {
               errors.add(new JMLValidationError(
                     "org.key_project.jmlediting.core.validationerror",
                     "Loop Specification followed by a non Loop Java Statement",
                     node));
            }
         }

      }
      return errors;
   }

   public boolean checkForLoop(final ASTNode node) {
      return (node instanceof ForStatement) || (node instanceof WhileStatement)
            || (node instanceof DoStatement);
   }
}
