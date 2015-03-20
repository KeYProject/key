package org.key_project.jmlediting.core.compilation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.compiler.BuildContext;
import org.eclipse.jdt.core.compiler.CategorizedProblem;
import org.eclipse.jdt.core.compiler.CompilationParticipant;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.compiler.ReconcileContext;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.internal.compiler.problem.DefaultProblemFactory;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.eclipse.jdt.internal.corext.dom.GenericVisitor;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLValidationError;
import org.key_project.jmlediting.core.validation.JMLValidationContext;
import org.key_project.jmlediting.core.validation.JMLValidationEngine;
import org.key_project.util.eclipse.Logger;

/**
 * This class takes part in the compilation process of the JDT to validate the
 * JML comments in the Java files. It does not modify anything in the
 * compilation process. Currently this class reports parse errors only, but
 * later on it could be used to report other problems (e.g. not available
 * variables).
 *
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
public class JMLCompilationParticipant extends CompilationParticipant {

   @Override
   public boolean isActive(final IJavaProject project) {
      return true;
   }

   @Override
   public void reconcile(final ReconcileContext context) {
      /*
       * In this method parse errors are reported as annotations. This method is
       * called for a source file when it changes (not as often as reconciling
       * for highlighting) but not as error markers, as this is done in Eclipse
       * too.
       */
      // We need a profile to do anything
      if (!JMLPreferencesHelper.isAnyProfileAvailable()) {
         return;
      }
      try {
         final String source = context.getWorkingCopy().getSource();
         final IResource res = context.getWorkingCopy().getResource();

         // Detect all comments in the file and then parse it
         final CommentLocator locator = new CommentLocator(source);
         for (final CommentRange jmlComment : locator.findJMLCommentRanges()) {
            final IJMLParser parser = JMLPreferencesHelper
                  .getProjectActiveJMLProfile(res.getProject()).createParser();
            try {
               parser.parse(source, jmlComment);
               // Throw away the result, here only a parse exception is
               // interesting
            }
            catch (final ParserException e) {
               final List<CategorizedProblem> problems = new ArrayList<CategorizedProblem>(
                     e.getAllErrors().size());

               // Create a problem for each parse error found
               for (final ParserError error : e.getAllErrors()) {
                  problems.add(new DefaultProblemFactory().createProblem(res
                        .getName().toCharArray(), IProblem.Syntax,
                        new String[] { error.getErrorMessage() },
                        new String[] { error.getErrorMessage() },
                        ProblemSeverities.Error, error.getErrorOffset(), error
                        .getErrorOffset(), -1, -1));
               }

               // And now put the problems to the context to make them visible
               context.putProblems(
                     "org.key_project.jmlediting.core.parseerror",
                     problems.toArray(new CategorizedProblem[problems.size()]));

            }
         }
      }
      catch (final JavaModelException e) {
         // If this occurs, something really strange happened (
         final Logger logger = new Logger(Activator.getDefault(),
               Activator.PLUGIN_ID);
         logger.logError("Unexpected exception when reconciling JML", e);
      }

   }

   @Override
   public void buildStarting(final BuildContext[] files, final boolean isBatch) {
      /*
       * Here the errors are reported as error markers which appear in the
       * problems list.
       */

      if (isBatch) {
         return;
      }
      for (final BuildContext context : files) {
         final IFile res = context.getFile();
         final String source = new String(context.getContents());
         // Remove all JML Error markers from the file
         ParseErrorMarkerUpdater.removeErrorMarkers(res);
         ValidationErrorMarkerUpdater.removeErrorMarkers(res);
         // Detect all comments in the file and then parse it
         final CommentLocator locator = new CommentLocator(source);
         final List<CommentRange> jmlComments = locator.findJMLCommentRanges();
         // Start Preparation for Validation
         final org.eclipse.jdt.core.dom.CompilationUnit ast;
         final ASTParser parser = ASTParser
               .newParser(ASTParser.K_COMPILATION_UNIT);
         parser.setKind(ASTParser.K_COMPILATION_UNIT);
         parser.setSource(source.toCharArray());
         parser.setResolveBindings(true);
         ast = (org.eclipse.jdt.core.dom.CompilationUnit) parser
               .createAST(null);
         final IJMLParser jmlParser = JMLPreferencesHelper
               .getProjectActiveJMLProfile(res.getProject()).createParser();

         final List<Comment> commentList = ast.getCommentList();
         final Map<Comment, ASTNode> inverse = new HashMap();
         final Map<Comment, ASTNode> inverseTrailing = new HashMap();
         final Map<CommentRange, Comment> jmlCommentToInverse = new HashMap();
         final Map<CommentRange, Comment> jmlCommentToInverseTrailing = new HashMap();
         ast.accept(new GenericVisitor() {
            @Override
            protected boolean visitNode(final ASTNode node) {
               // Maps All Leading Comments to its node
               // Also Maps JML comments to Comments, which are mapped to nodes
               final int start = ast.firstLeadingCommentIndex(node);
               final int end = ast.lastTrailingCommentIndex(node);

               if (start != -1) {
                  int pos = start;
                  while (pos < commentList.size()
                        && commentList.get(pos).getStartPosition() < node
                        .getStartPosition()) {
                     assert !inverse.containsKey(commentList.get(pos));
                     inverse.put(commentList.get(pos), node);
                     for (final CommentRange c : jmlComments) {
                        if (c.getBeginOffset() == commentList.get(pos)
                              .getStartPosition()) {
                           assert !jmlCommentToInverse.containsKey(c);
                           jmlCommentToInverse.put(c, commentList.get(pos));
                        }

                     }
                     pos++;

                  }

               }
               // Same as above for Trailing Comments
               if (end != -1) {
                  int pos = end;
                  while (pos >= 0
                        && commentList.get(pos).getStartPosition() > node
                              .getStartPosition()) {
                     assert !inverseTrailing.containsKey(commentList.get(pos));
                     inverseTrailing.put(commentList.get(pos), node);
                     for (final CommentRange c : jmlComments) {
                        if (c.getBeginOffset() == commentList.get(pos)
                              .getStartPosition()) {
                           assert !jmlCommentToInverseTrailing.containsKey(c);
                           jmlCommentToInverseTrailing.put(c,
                                 commentList.get(pos));
                        }

                     }
                     pos--;
                  }
               }

               return super.visitNode(node);
            }
         });

         for (final Entry<Comment, ASTNode> comments : inverse.entrySet()) {
            System.out.println("Assigned: " + comments.getKey() + " to "
                  + comments.getValue());
         }
         for (final Entry<CommentRange, Comment> comments : jmlCommentToInverse
               .entrySet()) {
            System.out.println("Assigned JMLComment: " + comments.getKey()
                  + " to " + comments.getValue());
         }
         final JMLValidationContext jmlContext = new JMLValidationContext(
               inverse, inverseTrailing, jmlCommentToInverse,
               jmlCommentToInverseTrailing, source, jmlComments, ast, jmlParser);
         final JMLValidationEngine engine = new JMLValidationEngine(
               JMLPreferencesHelper
               .getProjectActiveJMLProfile(res.getProject()),
               jmlContext);
         // End of Preparation
         final List<JMLValidationError> errors = new ArrayList<JMLValidationError>();
         for (final CommentRange jmlComment : jmlComments) {
            try {
               // System.out.println(""
               // + this.findCorrespondingNode(jmlComment.getBeginOffset(),
               // jmlComment.getEndOffset(), ast));
               final IASTNode node = jmlParser.parse(source, jmlComment);
               errors.addAll(engine.validateComment(node));
               // Throw away the result, here only a parse exception is
               // interesting
            }
            catch (final ParserException e) {
               // Add error markers for all parser exceptions
               ParseErrorMarkerUpdater.createErrorMarkers(res, source, e);
            }
         }
         // TODO: Unify ErrorMarkerUpdater
         ValidationErrorMarkerUpdater.createErrorMarkers(res, source, errors);
      }
   }
}
