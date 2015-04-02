package org.key_project.jmlediting.ui.util;

import java.util.Arrays;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;

/**
 * Provides several Methods needed for AutoCompletion.
 *
 * @author Thomas Glaser
 *
 */
public final class JMLCompletionUtil {
   /**
    * only static Access.
    */
   private JMLCompletionUtil() {

   }

   // not needed atm, but functionality may be needed sometimes
   /**
    * manually defined Proposals for KeywordProposals.
    */
   private static final List<String> CUSTOM_PROPOSALS = Arrays
         .asList(new String[0]);

   /**
    * Get all (filtered) JML Keyword-Proposals.
    *
    * @param context
    *           the {@link JavaContentAssistInvocationContext} to get the
    *           standardProposals for
    * @param proposalPrefix
    *           the prefix to compute the proposals for, null for the
    *           standardProposals
    * @param proposalImage
    *           the Image to be displayed in front of the proposal, null for no
    *           Image
    * @param sort
    *           the {@link IKeywordSort} of which all proposals have to be
    * @return List<{@link ICompletionProposal}> the computed standardProposals
    */
   public static List<ICompletionProposal> getKeywordProposals(
         final JavaContentAssistInvocationContext context,
         final String proposalPrefix, final Image proposalImage,
         final IKeywordSort sort) {
      if (sort == null) {
         throw new IllegalArgumentException("Sort may not be null!");
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
               .filterKeywords(currentJMLProfile, sort);

         // Iterate through the supported Keywords defined in JMLProfile
         for (final IKeyword keywordContainer : filteredKeywordList) {
            final Set<String> keywords = keywordContainer.getKeywords();
            // check for all spellings
            for (final String keyword : keywords) {
               // ignore not possible suggestions
               if (keyword.startsWith(prefix)
                     || keyword.startsWith("\\" + prefix)) {
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
            ToplevelKeywordSort.INSTANCE);
   }

   /**
    * compute the Prefix with respect to the parsed JML.
    *
    * @param context
    *           the context the completion is invoked from
    * @param node
    *           the parsed JML
    * @return the computed prefix
    */
   public static String computePrefix(
         final JavaContentAssistInvocationContext context, final IASTNode node) {
      String prefix = null;
      if (node.containsOffset(context.getInvocationOffset() - 1)) {
         final IASTNode wordNode = Nodes.getDepthMostNodeWithPosition(
               context.getInvocationOffset() - 1, node);
         // the cursor is in the current Node => substring
         prefix = context
               .getDocument()
               .get()
               .substring(wordNode.getStartOffset(),
                     context.getInvocationOffset());
      }
      else if (node.getStartOffset() >= context.getInvocationOffset()) {
         // the node is after the cursor => empty prefix and break the
         // recursion
         prefix = "";
      }

      // ignore . as a prefix
      if (prefix != null && prefix.equals(".")) {
         prefix = "";
      }
      return prefix;
   }
}
