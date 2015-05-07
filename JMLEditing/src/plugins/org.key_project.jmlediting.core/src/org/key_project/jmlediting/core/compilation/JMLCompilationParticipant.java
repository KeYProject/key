package org.key_project.jmlediting.core.compilation;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.compiler.BuildContext;
import org.eclipse.jdt.core.compiler.CategorizedProblem;
import org.eclipse.jdt.core.compiler.CompilationParticipant;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.compiler.ReconcileContext;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.internal.compiler.problem.DefaultProblemFactory;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.ErrorMarkerUpdater;
import org.key_project.jmlediting.core.utilities.ErrorTypes;
import org.key_project.jmlediting.core.utilities.JMLError;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.core.validation.JMLValidationContext;
import org.key_project.jmlediting.core.validation.JMLValidationEngine;
import org.key_project.util.jdt.JDTUtil;

/**
 * This class takes part in the compilation process of the JDT to validate the
 * JML comments in the Java files. It does not modify anything in the
 * compilation process.
 *
 * @author Moritz Lichter, David Giessing
 *
 */
@SuppressWarnings("restriction")
public class JMLCompilationParticipant extends CompilationParticipant {

   @Override
   public boolean isActive(final IJavaProject project) {
      // Always enabled, even though JML Editing is not enabled to get clean
      // requests
      // to remove old markers after JML Editing has been disabled
      return true;
   }

   @Override
   public void cleanStarting(final IJavaProject project) {
      super.cleanStarting(project);
      // Remove all JML Marks from all files in the project
      try {
         project.getProject().accept(new IResourceVisitor() {

            @Override
            public boolean visit(final IResource resource) throws CoreException {
               if (resource instanceof IFile) {
                  ErrorMarkerUpdater.removeErrorMarkers(resource);
               }
               return true;
            }
         });
      }
      catch (final CoreException e) {
         // If this occurs, something really strange happened!
         LogUtil.getLogger().logError("Unexpected exception when cleaning JML", e);
      }
   }

   @Override
   public void reconcile(final ReconcileContext context) {
      if (!JMLPreferencesHelper.isExtensionEnabled()) {
         return;
      }
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
         // If this occurs, something really strange happened
         LogUtil.getLogger().logError("Unexpected exception when reconciling JML", e);
      }

   }

   @Override
   public void buildStarting(final BuildContext[] files, final boolean isBatch) {
      if (!JMLPreferencesHelper.isExtensionEnabled()) {
         return;
      }
      /*
       * Here the errors are reported as error markers which appear in the
       * problems list.
       */
      for (final BuildContext context : files) {
         final IFile res = context.getFile();
         final String source = new String(context.getContents());
         // Remove all JML Error markers from the file
         ErrorMarkerUpdater.removeErrorMarkers(res);
         // Detect all comments in the file and then parse it
         final CommentLocator locator = new CommentLocator(source);
         final List<CommentRange> jmlComments = locator.findJMLCommentRanges();
         // Start Preparation for Validation
         // Setup JDT Parser and Create JDT AST
         final org.eclipse.jdt.core.dom.CompilationUnit ast = (org.eclipse.jdt.core.dom.CompilationUnit) JDTUtil.parse(source);
         // Setup jmlParser
         final IJMLParser jmlParser = JMLPreferencesHelper
               .getProjectActiveJMLProfile(res.getProject()).createParser();
         // Setup JML Validation engine
         final JMLValidationEngine engine = this.prepareValidation(ast,
               jmlComments, jmlParser, res, source);
         // End of Preparation
         final List<JMLError> allErrors = new ArrayList<JMLError>();
         for (final CommentRange jmlComment : jmlComments) {
            try {
               final IASTNode node = jmlParser.parse(source, jmlComment);
               allErrors.addAll(engine.validateComment(jmlComment, node));
               // addAll ValidationErrors
            }
            catch (final ParserException e) {
               // Add error markers for all parser exceptions
               allErrors.addAll(this.convertParseException(e));

            }
         }
         // Create ALL ErrorMarkers
         ErrorMarkerUpdater.createErrorMarker(allErrors, res, source);
      }
   }

   /**
    * Prepares Validation. Sets up the ValidationEngine and the Validation
    * Context.
    *
    * @param jdtAST
    *           The JDT AST
    * @param jmlComments
    *           the List of JML Comments as CommentRanges
    * @param jmlParser
    *           the JML parser
    * @param res
    *           the Resource to operate on
    * @param src
    *           the Source
    * @return a JML Validation Engine, locked and fully loaded
    */
   private JMLValidationEngine prepareValidation(final CompilationUnit jdtAST,
         final List<CommentRange> jmlComments, final IJMLParser jmlParser,
         final IResource res, final String src) {
      @SuppressWarnings("unchecked")
      final List<Comment> commentList = jdtAST.getCommentList();
      // Map JMLComments to JDTComments
      final Map<CommentRange, Comment> jmlCommentToComment = new HashMap<CommentRange, Comment>();
      for (final CommentRange c : jmlComments) {
         for (final Comment jdtComment : commentList) {
            if (c.getBeginOffset() == jdtComment.getStartPosition()) {
               jmlCommentToComment.put(c, jdtComment);
            }
         }

      }
      final Map<Comment, ASTNode> inverse = new HashMap<Comment, ASTNode>();
      jdtAST.accept(new ASTVisitor() {
         @Override
         public boolean preVisit2(final ASTNode node) {
            // Maps All Leading Comments to its node
            // Also Maps JML comments to Comments, which are mapped to nodes
            final int start = jdtAST.firstLeadingCommentIndex(node);
            if (start != -1) {
               int pos = start;
               while (pos < commentList.size() && 
                      commentList.get(pos).getStartPosition() < node.getStartPosition()) {
                  Comment comment = commentList.get(pos);
                  assert !inverse.containsKey(comment);
                  inverse.put(comment, node);
                  pos++;

               }

            }
            return super.preVisit2(node);
         }
      });
      final JMLValidationContext jmlContext = new JMLValidationContext(inverse,
            jmlCommentToComment, src, jmlComments, jdtAST,
            jmlParser);
      return new JMLValidationEngine(
            JMLPreferencesHelper.getProjectActiveJMLProfile(res.getProject()),
            jmlContext);
   }

   /**
    * Converts Parse Exceptions to JMLErrors. Needed to unify
    * ErrorMarkerUpdater.
    *
    * @param e
    *           the parse Exception
    * @return the List of JML Errors extracted from e
    */
   private List<JMLError> convertParseException(final ParserException e) {
      final List<JMLError> converted = new ArrayList<JMLError>();
      for (final ParserError err : e.getAllErrors()) {
         converted.add(new JMLError("", ErrorTypes.ParseError, err
               .getErrorMessage(), err.getErrorOffset()));
      }
      return converted;
   }
}
