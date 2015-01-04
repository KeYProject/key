package org.key_project.jmlediting.core.compilation;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.compiler.CategorizedProblem;
import org.eclipse.jdt.core.compiler.CompilationParticipant;
import org.eclipse.jdt.core.compiler.IProblem;
import org.eclipse.jdt.core.compiler.ReconcileContext;
import org.eclipse.jdt.internal.compiler.problem.DefaultProblemFactory;
import org.eclipse.jdt.internal.compiler.problem.ProblemSeverities;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserError;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
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
}
