package org.key_project.jmlediting.ui.completion;

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
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;
import org.key_project.jmlediting.ui.util.JMLEditingImages;

/**
 * An {@link IJavaCompletionProposalComputer} to support JML.
 *
 * @author Martin Hentschel
 * @author Thomas Glaser
 */
public class JMLCompletionProposalComputer implements
      IJavaCompletionProposalComputer {

   /**
    *
    * @return the KeY-Image for the Keyword-Proposals
    */
   public static Image getJMLImg() {
      return JMLEditingImages.getImage(JMLEditingImages.JML_LOGO);
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
         IASTNode parseResult = null;
         final String docText = context.getDocument().get();
         try {
            // Parse the text
            // End index of comment is inclusive, but input end for parser
            // exclusive
            parseResult = parser.parse(docText, comment);

         }
         catch (final ParserException e) {
            parseResult = e.getErrorNode();
         }

         // If Parser could parse or complete Error Recovery
         if (parseResult != null) {
            final int caretPosition = context.getInvocationOffset();
            // Get keyword application node
            final IASTNode keywordApplNode = Nodes
                  .getNodeAtCaretPositionIncludeRightWhiteSpace(parseResult,
                        caretPosition, NodeTypes.KEYWORD_APPL);
            // Check that there is a keyword appl and the caret not on the
            // keyword itself
            if (keywordApplNode != null) {

               // Check whether the caret is in the keyword content
               final boolean caretOnKeyword = keywordApplNode.getChildren()
                     .get(0).containsCaret(caretPosition);

               // Caret is not allowed to be on the keyword itself and not at
               // the end of the keyword (or on whitespace) if the keywrod does
               // not contains a toplevel error (e.g. missing semicolon)

               final boolean onContent = isCaretOnKeywordContent(
                     keywordApplNode, caretPosition)
                     || hasToplevelError(keywordApplNode);

               if (!caretOnKeyword && onContent) {
                  // Get the keyword from the node and get result of
                  // autoproposals
                  final IKeyword activeKeyword = ((IKeywordNode) keywordApplNode
                        .getChildren().get(0)).getKeyword();

                  final IKeywordAutoProposer proposer = activeKeyword
                        .createAutoProposer();
                  if (proposer != null) {
                     final List<ICompletionProposal> proposals = proposer
                           .createAutoProposals(keywordApplNode, javaContext);
                     if (proposals != null) {
                        result.addAll(proposals);
                     }
                     else {
                        result.addAll(this.proposeToplevelKeywords(javaContext));
                     }
                  }
                  else if (caretPosition == keywordApplNode.getEndOffset()
                        && docText.charAt(caretPosition - 1) == ';') {
                     // Default case: no specific auto proposer and semicolon
                     // closed keyword
                     return this.proposeToplevelKeywords(javaContext);
                  }
               }
               else {

                  return this.proposeToplevelKeywords(javaContext);
               }
            }
            else {
               return this.proposeToplevelKeywords(javaContext);
            }

            return result;
         }
         // Fallback Method to display all JML Keyword-Proposals, if
         // no active Keyword was discovered.
         return this.proposeToplevelKeywords(javaContext);
      }
      return result;

   }

   /**
    * Checks whether the given Node has an ErrorNode on the Top Level.
    *
    * @param keywordApplNode
    *           the Node to check
    * @return true if there is an Toplevel ErrorNode, else false
    */
   private static boolean hasToplevelError(final IASTNode keywordApplNode) {
      if (keywordApplNode.getChildren().size() == 1) {
         // EmptyKeyword
         return false;
      }
      final IASTNode keywordContent = keywordApplNode.getChildren().get(1);
      if (keywordContent.getType() == NodeTypes.ERROR_NODE) {
         return true;
      }
      if (keywordContent.getChildren().isEmpty()) {
         // Should not occur
         return false;
      }
      final IASTNode topContentNode = keywordContent.getChildren().get(0);
      return topContentNode.getType() == NodeTypes.ERROR_NODE;
   }

   /**
    * Checks whether a given caret is on a given Keywords Content.
    *
    * @param keywordApplNode
    *           the KeywordNode
    * @param caret
    *           the caret
    * @return true if the given Caret is on the keywords content.
    */
   private static boolean isCaretOnKeywordContent(
         final IASTNode keywordApplNode, final int caret) {

      if (keywordApplNode.getChildren().size() == 1) {
         // EmptyKeyword
         return keywordApplNode.containsCaret(caret);
      }
      final IASTNode keywordNode = keywordApplNode.getChildren().get(0);
      final IASTNode keywordContentNode = keywordApplNode.getChildren().get(1);
      return keywordNode.getEndOffset() <= caret
            && keywordContentNode.getEndOffset() >= caret;
   }

   /**
    * Propose all Toplevel Keywords.
    *
    * @param javaContext
    *           the context the proposal is invoked from
    * @return All Toplevel Keywords matching the prefix
    */
   private List<ICompletionProposal> proposeToplevelKeywords(
         final JavaContentAssistInvocationContext javaContext) {
      return JMLCompletionUtil.getStandardKeywordProposals(javaContext,
            getJMLImg());
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
