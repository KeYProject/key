package org.key_project.jmlediting.ui.completion;

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.ui.text.java.ContentAssistInvocationContext;
import org.eclipse.jdt.ui.text.java.IJavaCompletionProposalComputer;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.jface.text.contentassist.IContextInformation;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.ui.extension.JMLLocator;
import org.key_project.util.jmlediting.JMLUtil;

/**
 * An {@link IJavaCompletionProposalComputer} to support JML.
 *
 * @author Martin Hentschel
 * @author Thomas Glaser
 */
public class JMLCompletionProposalComputer implements
IJavaCompletionProposalComputer {
   private static final List<String> CUSTOM_PROPOSALS = Arrays
         .asList(new String[] { "also" });

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
         final JMLLocator locator = new JMLLocator(context.getDocument().get());
         if (locator.isInJMLcomment(context.getInvocationOffset())) {

            // getCurrentProject
            final IProject currentProject = JMLUtil.getCurrentProject();

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
                           prefixLength, keyword.length()));
                  }
               }
            }
            // Iterate through all JML-Profile independent keywords, like "also"
            for (final String keyword : CUSTOM_PROPOSALS) {
               // ignore not possible suggestions
               if (keyword.startsWith(prefix)) {
                  result.add(new CompletionProposal(keyword, proposalOffset,
                        prefixLength, keyword.length()));
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
