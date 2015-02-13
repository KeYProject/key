package org.key_project.jmlediting.core.validation;

import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IFile;
import org.eclipse.jdt.core.dom.ASTParser;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLValidationEngine {

   /**
    * validates all JMLSpecifications that can be validated via the Profile
    * specific Validators. If a Specification is not Valid ErrorMarkers are
    * added to the IFile res
    *
    * @param res
    *           The IFile to add the Markers to
    * @param src
    *           The Source on which to operate.
    */
   public static void validateAll(final IFile res, final String src,
         final List<CommentRange> jmlComments) {
      final org.eclipse.jdt.core.dom.CompilationUnit ast;
      final ASTParser parser = ASTParser
            .newParser(ASTParser.K_COMPILATION_UNIT);
      parser.setKind(ASTParser.K_COMPILATION_UNIT);
      parser.setSource(src.toCharArray());
      parser.setResolveBindings(true);
      ast = (org.eclipse.jdt.core.dom.CompilationUnit) parser.createAST(null);

      final Set<IJMLValidator> validator = JMLPreferencesHelper
            .getProjectActiveJMLProfile(res.getProject()).getValidator();
      final IJMLParser jmlParser = JMLPreferencesHelper
            .getProjectActiveJMLProfile(res.getProject()).createParser();

      final IJMLValidationContext context = new JMLValidationContext(src,
            jmlComments, ast);
      for (final IJMLValidator jmlValidator : validator) {
         for (final CommentRange commentRange : jmlComments) {
            IASTNode parseResult;
            try {
               parseResult = jmlParser.parse(src, commentRange);
            }
            catch (final ParserException e) {
               // could not Parse therefore no Verification possible
               continue;
            }
            jmlValidator.validate(context, parseResult);
         }
      }
   }
}
