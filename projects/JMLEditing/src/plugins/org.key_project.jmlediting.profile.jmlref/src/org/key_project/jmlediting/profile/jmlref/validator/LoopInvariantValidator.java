package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LoopNodeVisitor;
import org.key_project.jmlediting.core.validation.IJMLValidationContext;
import org.key_project.jmlediting.core.validation.JMLPositionValidator;

public class LoopInvariantValidator extends JMLPositionValidator {

   List<ASTNode> loopNodes = Collections.emptyList();

   @Override
   public List<IMarker> validate(final IJMLValidationContext context,
         final IASTNode node) {
      final CompilationUnit ast = context.getJavaAST();
      final LoopNodeVisitor visitor = new LoopNodeVisitor();
      ast.accept(visitor);
      visitor.visit(ast);
      visitor.visit(ast);
      visitor.visit(ast);
      this.loopNodes = visitor.getLoopNodes();
      // TODO find Invariant Nodes in JML (node)
      // TODO call Validate node for each of this
      return null;
   }

   @Override
   protected IMarker validateNode(final IJMLValidationContext context,
         final IASTNode node) {
      // TODO check comment for more jml that is not an invariant -> ret false
      // find Loop offset that is following the invariant
      ASTNode loopNode = null;
      for (final ASTNode lNode : this.loopNodes) {
         // Position is not doing its task better get an offset
         if (lNode.getStartPosition() > node.getStartOffset()) {
            // Loop found
            loopNode = lNode;
            break;
         }
      }
      if (loopNode == null) {
         // Invariant without loop following --> Invalid
         // TODO: Create IMarker
         return null;
      }

      // check for JML commments between invariant and loop offset
      final CommentLocator loc = new CommentLocator(context.getSrc());
      for (final CommentRange comment : context.getJMLComments()) {
         if (comment.getBeginOffset() > node.getStartOffset()
               && comment.getBeginOffset() < loopNode.getStartPosition()) {
            ;
            // TODO: check them for jml that is not an invariant
         }
      }
      // If Java Code final is found between final the Loop invariant final and
      // the next final Loops
      // offset, the invariant is invalid
      if (this.javaFoundBetween(node.getStartOffset(),
            loopNode.getStartPosition(), context.getSrc())) {
         // TODO: Create IMarker
         return null;
      }
      // Valid
      return null;
   }

   private static enum ScannerState {
      IN_COMMENT, DEFAULT
   }

   /**
    * Checks whether there is JavaCode between the begin Index and the begin of
    * the Loop in source
    *
    * @param begin
    *           The begin index from where to search
    * @param beginLoop
    *           the index the loop statement begins
    * @param source
    *           the source to search in
    * @return true if javaCode was found between begin and beginLoop
    */
   private boolean javaFoundBetween(final int begin, final int beginLoop,
         final String source) {
      final boolean javaFound = false;
      final char[] content = source.toCharArray();
      int position = begin;
      ScannerState state = ScannerState.DEFAULT;

      mainloop: while (position < beginLoop) {
         final char c = content[position];
         switch (state) {
         // DefaultState
         case DEFAULT:
            switch (c) {
            // comment opener found
            case '/':
               if (position < content.length - 1) {
                  final char c2 = content[position + 1];
                  switch (c2) {
                  // singleLine Comment found
                  case '/':
                     final int end = source.indexOf('\n', position);
                     position = end + 1;
                     break;
                  // Multiline Comment Opener found
                  case '*':
                     position += 2;
                     state = ScannerState.IN_COMMENT;
                     break;
                  // wrong combination of signs, ignore because there will be
                  // compile errors
                  default:
                     position += 1;
                     state = ScannerState.DEFAULT;
                     break;
                  }
               }
               else {
                  break mainloop;
               }
               break;
            // no special sign found
            default:
               if (Character.isJavaIdentifierStart(c)) {
                  return true;
               }
               position += 1;
               break;
            }
            break;
         case IN_COMMENT:
            switch (c) {
            // possible begin of MultilineComment Closer found
            case '*':
               if (position < content.length - 1) {
                  final char c2 = content[position + 1];
                  switch (c2) {
                  // MultiLine Comment Closer found
                  case '/':
                     state = ScannerState.DEFAULT;
                     position += 2;
                     break;
                  // star found, can be ignored because no / was found after
                  default:
                     position += 1;
                     break;
                  }
               }
               else {
                  break mainloop;
               }
               break;
            // no special sign found
            default:
               position += 1;
               break;
            }
            break;
         // in unexpected state
         default:
            throw new AssertionError("Invalid Enum State");
         }
      }
      return javaFound;
   }
}
