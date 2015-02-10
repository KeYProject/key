package org.key_project.jmlediting.profile.jmlref.validator;

import org.eclipse.jdt.core.dom.ASTParser;
import org.key_project.jmlediting.core.utilities.Position;

public class LoopInvariantValidator extends JMLPositionValidator {

   @Override
   boolean isValidForPosition(final IJMLValidationContext context,
         final Position p) {
      final org.eclipse.jdt.core.dom.CompilationUnit ast;
      final ASTParser parser = ASTParser
            .newParser(ASTParser.K_COMPILATION_UNIT);
      parser.setKind(ASTParser.K_COMPILATION_UNIT);
      parser.setSource(context.getCompilationUnit());
      parser.setResolveBindings(true);
      ast = (org.eclipse.jdt.core.dom.CompilationUnit) parser.createAST(null);
      // TODO Auto-generated method stub
      return false;
   }

}
