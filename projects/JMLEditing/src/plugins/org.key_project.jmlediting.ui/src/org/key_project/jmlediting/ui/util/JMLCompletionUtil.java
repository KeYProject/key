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
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IToplevelKeyword;

public class JMLCompletionUtil {
   private JMLCompletionUtil() {

   }

   // not needed atm, but functionality may be needed sometimes
   private static final List<String> CUSTOM_PROPOSALS = Arrays
         .asList(new String[0]);

   /**
    * Get all (filtered) JML Keyword-Proposals.
    *
    * @param context
    *           the {@link JavaContentAssistInvocationContext} to get the
    *           standardProposals for
    * @param prefix
    *           the prefix to compute the proposals for, null for the
    *           standardProposals
    * @param proposalImage
    *           the Image to be displayed in front of the proposal, null for no
    *           Image
    * @param filter
    *           the Class extending {@link IKeyword} to filter the proposals
    * @return List<{@link ICompletionProposal}> the computed standardProposals
    */
   public static List<ICompletionProposal> getKeywordProposals(
         final JavaContentAssistInvocationContext context,
         final String proposalPrefix, final Image proposalImage,
         final Class<? extends IKeyword> filter) {
      if (filter == null) {
         throw new IllegalArgumentException("filter may not be null!");
      }
      final List<ICompletionProposal> result = new LinkedList<ICompletionProposal>();

      // Load the specific JMLProfile for the current Project.
      final IJMLProfile currentJMLProfile = JMLPreferencesHelper
            .getProjectActiveJMLProfile(context.getProject().getProject());

      try {
         final String prefix;
         if (proposalPrefix == null) {
            prefix = context.computeIdentifierPrefix().toString();
         }
         else {
            prefix = proposalPrefix;
         }
         final int prefixLength = prefix.length();

         // compute the offset for replacing the prefix
         final int proposalOffset = context.getInvocationOffset()
               - prefixLength;

         // get only the Keywords that match the filter
         final Set<IKeyword> filteredKeywordList = JMLProfileHelper
               .filterKeywords(currentJMLProfile, filter);

         // Iterate through the supported Keywords defined in JMLProfile
         for (final IKeyword keywordContainer : filteredKeywordList) {
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

   /**
    * @see JMLCompletionUtil.getProposals( final
    *      JavaContentAssistInvocationContext context, final Image
    *      proposalImage, final Class<? extends IKeyword> filter)
    */
   public static List<ICompletionProposal> getStandardKeywordProposals(
         final JavaContentAssistInvocationContext context,
         final Image proposalImage) {
      return getKeywordProposals(context, null, proposalImage,
            IToplevelKeyword.class);
   }
}
