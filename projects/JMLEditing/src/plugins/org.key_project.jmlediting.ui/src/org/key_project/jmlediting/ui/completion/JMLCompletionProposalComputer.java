package org.key_project.jmlediting.ui.completion;

import java.io.IOException;
import java.net.URL;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageLoader;
import org.eclipse.swt.widgets.Display;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

/**
 * An {@link IJavaCompletionProposalComputer} to support JML.
 *
 * @author Martin Hentschel
 * @author Thomas Glaser
 */
public class JMLCompletionProposalComputer implements
      IJavaCompletionProposalComputer {

   private static Image img = null;

   private static Image getJMLImg() {
      if (img != null) {
         return img;
      }
      try {
         return new Image(Display.getCurrent(), new ImageLoader().load(new URL(
               "platform:/plugin/org.key_project.jmlediting.ui/icons/jml.png")
               .openStream())[0]);
      }
      catch (final IOException ioe) {
         return null;
      }
   }

   @Override
   public void sessionStarted() {
   }

   @Override
   public List<ICompletionProposal> computeCompletionProposals(
         final ContentAssistInvocationContext context,
         final IProgressMonitor monitor) {
      // Can only provide anything if there is a valid profile
      if (!JMLPreferencesHelper.isAnyProfileAvailable()) {
         return Collections.emptyList();
      }

      final List<ICompletionProposal> result = new LinkedList<ICompletionProposal>();

      final CommentLocator locator = new CommentLocator(context.getDocument()
            .get());
      final CommentRange comment = locator.getJMLComment(context
            .getInvocationOffset());

      // add proposals only if Content Assist is invoked in JML Code
      // get the prefix to filter only fitting keywords
      if (comment != null) {
         IProject currentProject;
         JavaContentAssistInvocationContext javaContext = null;
         if (context instanceof JavaContentAssistInvocationContext) {
            javaContext = (JavaContentAssistInvocationContext) context;
            currentProject = javaContext.getProject().getProject();
         }
         else {
            return result;
         }

         final IJMLProfile currentJMLProfile = JMLPreferencesHelper
               .getProjectActiveJMLProfile(currentProject);

         final IJMLParser parser = currentJMLProfile.createParser();
         try {
            // Parse the text
            // End index of comment is inclusive, but input end for parser
            // exclusive
            final IASTNode parseResult = parser.parse(context.getDocument()
                  .get(), comment.getContentBeginOffset(), comment
                  .getContentEndOffset() + 1);
            final IKeyword activeKeyword = Nodes.getKeywordNode(parseResult,
                  context.getInvocationOffset());
            if (activeKeyword != null) {

               result.addAll(activeKeyword.createAutoProposals(parseResult,
                     javaContext));
            }
            else {
               return JMLCompletionUtil.getStandardProposals(javaContext,
                     getJMLImg());
            }

         }
         catch (final ParserException e) {
            // Fallback Method to display all JML Keyword-Proposals, if Parser
            // fails.
            return JMLCompletionUtil.getStandardProposals(javaContext,
                  getJMLImg());
         }
      }
      return result;

   }

   @Override
   public List<IContextInformation> computeContextInformation(
         final ContentAssistInvocationContext context,
         final IProgressMonitor monitor) {
      return Collections.emptyList();
   }

   @Override
   public String getErrorMessage() {
      return null;
   }

   @Override
   public void sessionEnded() {
   }
}
