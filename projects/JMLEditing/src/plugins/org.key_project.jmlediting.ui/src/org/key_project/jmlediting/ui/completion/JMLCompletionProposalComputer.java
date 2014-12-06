package org.key_project.jmlediting.ui.completion;

import java.io.IOException;
import java.net.URL;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.ImageLoader;
import org.eclipse.swt.widgets.Display;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.extension.CommentLocator;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * An {@link IJavaCompletionProposalComputer} to support JML.
 *
 * @author Martin Hentschel
 * @author Thomas Glaser
 */
public class JMLCompletionProposalComputer implements
      IJavaCompletionProposalComputer {

   // not needed atm, but functionality may be needed sometimes
   private static final List<String> CUSTOM_PROPOSALS = Arrays
         .asList(new String[0]);

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
      final List<ICompletionProposal> result = new LinkedList<ICompletionProposal>();

      try {
         // add proposals only if Content Assist is invoked in JML Code
         final CommentLocator locator = new CommentLocator(context.getDocument().get());
         if (locator.isInJMLcomment(context.getInvocationOffset())) {

            // getCurrentProject
            IProject currentProject;
            if (context instanceof JavaContentAssistInvocationContext) {
               final JavaContentAssistInvocationContext javaContext = (JavaContentAssistInvocationContext) context;
               currentProject = javaContext.getProject().getProject();
            }
            else {
               currentProject = WorkbenchUtil.getCurrentProject();
               if (currentProject == null) {
                  return result;
               }
            }

            // Load the specific JMLProfile for the current Project.
            final IJMLProfile currentJMLProfile = JMLPreferencesHelper
                  .getProjectActiveJMLProfile(currentProject);

            // get the prefix to filter only fitting keywords
            final String prefix = context.computeIdentifierPrefix().toString();
            final int prefixLength = prefix.length();

            // compute the offset for replacing the prefix
            final int proposalOffset = context.getInvocationOffset()
                  - prefix.length();

            // Iterate through the supported behaviors defined in JMLProfile
            for (final IKeyword behavior : currentJMLProfile
                  .getSupportedKeywords()) {
               final Set<String> keywords = behavior.getKeywords();
               // check for all spellings
               for (final String keyword : keywords) {
                  // ignore not possible suggestions
                  if (keyword.startsWith(prefix)) {
                     result.add(new CompletionProposal(keyword, proposalOffset,
                           prefixLength, keyword.length(), getJMLImg(), null,
                           null, null));
                  }
               }
            }
            // Iterate through all JML-Profile independent keywords, like "also"
            for (final String keyword : CUSTOM_PROPOSALS) {
               // ignore not possible suggestions
               if (keyword.startsWith(prefix)) {
                  result.add(new CompletionProposal(keyword, proposalOffset,
                        prefixLength, keyword.length(), getJMLImg(), null,
                        null, null));
               }
            }
         }
      }
      catch (final Exception e) {
         e.printStackTrace();
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
