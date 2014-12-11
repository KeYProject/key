package org.key_project.jmlediting.ui.util;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class JMLCompletionUtil {
   private JMLCompletionUtil() {

   }

   // not needed atm, but functionality may be needed sometimes
   private static final List<String> CUSTOM_PROPOSALS = Arrays
         .asList(new String[0]);

   /**
    * Fallback Method to display all JML Keyword-Proposals, if Parser fails.
    *
    * @param context
    *           the {@link JavaContentAssistInvocationContext} to get the
    *           standardProposals for
    * @return the computed standardProposals
    */
   public static List<ICompletionProposal> getStandardProposals(
         final JavaContentAssistInvocationContext context,
         final Image proposalImage, final Class<? extends IKeyword> filter) {
      final List<ICompletionProposal> result = new LinkedList<ICompletionProposal>();

      // Load the specific JMLProfile for the current Project.
      final IJMLProfile currentJMLProfile = JMLPreferencesHelper
            .getProjectActiveJMLProfile(context.getProject().getProject());

      try {
         // add proposals only if Content Assist is invoked in JML Code
         // get the prefix to filter only fitting keywords
         final String prefix = context.computeIdentifierPrefix().toString();
         final int prefixLength = prefix.length();

         // compute the offset for replacing the prefix
         final int proposalOffset = context.getInvocationOffset()
               - prefix.length();

         // Iterate through the supported Keywords defined in JMLProfile
         for (final IKeyword keywordContainer : currentJMLProfile
               .getSupportedKeywords()) {
            if (filter.isAssignableFrom(keywordContainer.getClass())) {
               final Set<String> keywords = keywordContainer.getKeywords();
               // check for all spellings
               for (final String keyword : keywords) {
                  // ignore not possible suggestions
                  if (keyword.startsWith(prefix)) {
                     result.add(new CompletionProposal(keyword, proposalOffset,
                           prefixLength, keyword.length(), proposalImage, null,
                           null, null));
                  }
               }
            }
         }
         // Iterate through all JML-Profile independent keywords, like "also"
         for (final String keyword : CUSTOM_PROPOSALS) {
            // ignore not possible suggestions
            if (keyword.startsWith(prefix)) {
               result.add(new CompletionProposal(keyword, proposalOffset,
                     prefixLength, keyword.length(), proposalImage, null, null,
                     null));
            }
         }
      }
      catch (final Exception e) {
         e.printStackTrace();
      }
      return result;
   }
}
