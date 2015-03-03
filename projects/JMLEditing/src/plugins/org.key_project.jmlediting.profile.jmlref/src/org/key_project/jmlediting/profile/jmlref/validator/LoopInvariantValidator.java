package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.utilities.LoopNodeVisitor;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;
import org.key_project.jmlediting.core.validation.JMLKeywordValidator;
import org.key_project.jmlediting.core.validation.JavaCodeVisitor;
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
   private List<ASTNode> loopNodes = new ArrayList<ASTNode>();
   private final List<IKeywordNode> keywords = new ArrayList<IKeywordNode>();
   private CommentRange containingComment;

   @Override
   public List<JMLValidationError> validate(
         final IJMLValidationContext context, final IASTNode node) {
      final List<JMLValidationError> error = new ArrayList<JMLValidationError>();
      final CompilationUnit ast = context.getJavaAST();
      final LoopNodeVisitor visitor = new LoopNodeVisitor();
      ast.accept(visitor);
      this.loopNodes = visitor.getLoopNodes();
      final List<IASTNode> keywordNodes = Nodes.getAllNodesOfType(node,
            NodeTypes.KEYWORD);
      for (final IASTNode iastNode : keywordNodes) {
         this.keywords.add((IKeywordNode) iastNode);
      }
      // Filter List for Invariant Keywords
      JMLValidationError keywordError = null;
      for (final IKeywordNode iKeywordNode : this.keywords) {
         if ((iKeywordNode.getKeyword() instanceof LoopInvariantKeyword)
               || (iKeywordNode.getKeyword() instanceof DecreasingKeyword)) {
            // Validate the Loop Keywords
            keywordError = this.validateNode(context, iKeywordNode);
            if (keywordError != null) {
               error.add(keywordError);
            }
         }

      }
      return error;
   }

   /**
    * Method for checking if a given JML Specification represented by node is
    * valid.
    *
    * @param context
    *           the Validation Context
    * @param node
    *           the Specification to validate
    * @return an IMarker if the Specification is invalid, null if it is valid
    */
   protected JMLValidationError validateNode(
         final IJMLValidationContext context, final IASTNode node) {
      // find Loop offset that is following the invariant
      ASTNode loopNode = null;
      for (final ASTNode lNode : this.loopNodes) {
         if (lNode.getStartPosition() > node.getStartOffset()) {
            // Loop found
            loopNode = lNode;
            break;
         }
      }
      if (loopNode == null) {
         // Invariant without loop following --> Invalid
         return new JMLValidationError(
               "org.key_project.jmlediting.core.validationerror",
               "No Loop found after LoopInvariant or Decreasing Keyword", node);
      }
      // If Java Code is found between the Loop invariant and
      // the next Loops offset, the invariant is invalid
      for (final CommentRange r : context.getJMLComments()) {
         if (r.getBeginOffset() <= node.getStartOffset()
               && node.getEndOffset() <= r.getEndOffset()) {
            this.containingComment = r;
         }
      }
      if (this.javaFoundBetweenAST(this.containingComment.getEndOffset(),
            loopNode.getStartPosition(), context.getJavaAST())) {
         return new JMLValidationError(
               "org.key_project.jmlediting.core.validationerror",
               "Loop Specification followed by a non Loop Java Statement", node);
      }
      // Valid
      return null;
   }

   private boolean javaFoundBetweenAST(final int offset,
         final int loopNodeStart, final ASTNode javaAST) {
      final JavaCodeVisitor visitor = new JavaCodeVisitor(offset, loopNodeStart);
      javaAST.accept(visitor);
      return visitor.getNodeAfterComment() != null;
   }
}
