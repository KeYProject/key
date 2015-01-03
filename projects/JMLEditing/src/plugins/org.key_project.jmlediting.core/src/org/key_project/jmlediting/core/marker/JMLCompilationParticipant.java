package org.key_project.jmlediting.core.marker;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.compiler.CompilationParticipant;
import org.eclipse.jdt.core.compiler.ReconcileContext;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLCompilationParticipant extends CompilationParticipant {
   private IJavaProject p;

   @Override
   public boolean isActive(final IJavaProject project) {
      this.p = project;
      return true;
   }

   @Override
   public void reconcile(final ReconcileContext context) {
      System.out.println("Reconcile");
      try {
         final String source = context.getWorkingCopy().getSource();
         final CommentLocator locator = new CommentLocator(source);
         for (final CommentRange jmlComment : locator.findJMLCommentRanges()) {
            final IJMLParser parser = JMLPreferencesHelper
                  .getProjectActiveJMLProfile(this.p.getProject())
                  .createParser();
            try {
               parser.parse(source, jmlComment.getContentBeginOffset(),
                     jmlComment.getContentEndOffset() + 1);
            }
            catch (final ParserException e) {
               /*
                * final List<CategorizedProblem> problems = new
                * ArrayList<CategorizedProblem>( e.getAllErrors().size());
                * 
                * for (final ParserError error : e.getAllErrors()) {
                * problems.add(new DefaultProblem(null, error.getErrorMessage(),
                * 0, null, ProblemSeverities.Error, error.getErrorOffset(),
                * error .getErrorOffset(), 10, 5));
                * 
                * } context.putProblems(
                * "org.key_project.jmlediting.core.parseerror",
                * problems.toArray(new CategorizedProblem[problems.size()]));
                */
               try {
                  ParseErrorMarkerUpdater.createErrorMarkers(context
                        .getWorkingCopy().getResource(), source, e, jmlComment);
               }
               catch (final CoreException e1) {
                  // TODO Auto-generated catch block
                  e1.printStackTrace();
               }
            }
         }
      }
      catch (final JavaModelException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }
   }
}
