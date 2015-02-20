package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.utilities.LoopNodeVisitor;
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
   private List<ASTNode> loopNodes = Collections.emptyList();
   private final List<IKeywordNode> keywords = Collections.emptyList();
   private CommentRange containingComment;

   @Override
   public List<JMLValidationError> validate(
         final IJMLValidationContext context, final IASTNode node) {
      final List<JMLValidationError> error = Collections.emptyList();
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

      // check for JML commments between invariant and loop offset and check
      // comment containing the keyword to check
      for (final CommentRange comment : context.getJMLComments()) {
         if (comment.getEndOffset() > node.getStartOffset()
               && comment.getBeginOffset() < loopNode.getStartPosition()) {
            if (comment.getBeginOffset() < node.getStartOffset()
                  && comment.getEndOffset() > node.getStartOffset()) {
               this.containingComment = comment;
            }
            try {
               final IASTNode ast = context.getJMLParser().parse(
                     context.getSrc(), comment);
               final List<IKeywordNode> keywords = Nodes.getAllKeywords(ast);
               for (final IKeywordNode iKeywordNode : keywords) {
                  // Check for Keywords that are no Invariant
                  // If Keyword is before the Invariant that has to be
                  // checked
                  // ignore it
                  if (iKeywordNode.getStartOffset() > node.getStartOffset()
                        && (iKeywordNode.getKeyword() instanceof LoopInvariantKeyword || iKeywordNode
                              .getKeyword() instanceof DecreasingKeyword)) {
                     continue;
                  }
                  else {
                     // illegal JML Statement after Loop Specification
                     return new JMLValidationError(
                           "org.key_project.jmlediting.core.validationerror",
                           "Non LoopInvariant or Decreasing Keyword found following the Loop Specification",
                           node);
                  }
               }
            }
            catch (final ParserException e) {
               // Comment could not be parsed, ignore it and go on with the
               // next
               continue;
            }
         }
      }

      // If Java Code is found between the Loop invariant and
      // the next Loops offset, the invariant is invalid
      if (this.javaFoundBetween(this.containingComment.getEndOffset(),
            loopNode.getStartPosition(), context.getSrc())) {
         return new JMLValidationError(
               "org.key_project.jmlediting.core.validationerror",
               "Loop Specification not followed by a Loop", node);
      }
      // Valid
      return null;
   }

   private static enum ScannerState {
      IN_COMMENT, DEFAULT
   }

   /**
    * Checks whether there is JavaCode between the begin Index and the begin of
    * the Loop in source.
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
