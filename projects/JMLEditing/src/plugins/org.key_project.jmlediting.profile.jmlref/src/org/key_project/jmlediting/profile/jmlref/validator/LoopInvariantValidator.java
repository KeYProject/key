package org.key_project.jmlediting.profile.jmlref.validator;

import org.eclipse.jdt.core.dom.ASTParser;
import org.key_project.jmlediting.core.compilation.IJMLValidationContext;
import org.key_project.jmlediting.core.compilation.JMLPositionValidator;
import org.key_project.jmlediting.core.utilities.Position;

public class LoopInvariantValidator extends JMLPositionValidator {

   @Override
   protected boolean isValidForPosition(final IJMLValidationContext context,
         final Position p) {
      final org.eclipse.jdt.core.dom.CompilationUnit ast;
      final ASTParser parser = ASTParser
            .newParser(ASTParser.K_COMPILATION_UNIT);
      parser.setKind(ASTParser.K_COMPILATION_UNIT);
      parser.setSource(context.getSrc().toCharArray());
      parser.setResolveBindings(true);
      ast = (org.eclipse.jdt.core.dom.CompilationUnit) parser.createAST(null);
      // TODO check comment for more jml that is not an invariant -> ret false
      // TODO find Loop offset
      // TODO check for JML commments between invariant and loop offset
      // TODO: check them for jml that is not an invariant
      // If Java Code is found between the Loop invariant and the next Loops
      // offset, the invariant is invalid
      if (this.javaFoundBetween(p, beginLoop, context.getSrc())) {
         return false;
      }
      return true;
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
