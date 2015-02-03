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
      System.out
            .println("InvocationOffset == " + context.getInvocationOffset());

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
         try {
            // Parse the text
            // End index of comment is inclusive, but input end for parser
            // exclusive
            parseResult = parser.parse(context.getDocument().get(), comment);

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
               final boolean keywordTopLevelError;
               final boolean caretAtEndOrOnRightWhiteSpace;
               if (keywordApplNode.getChildren().size() == 1) {
                  keywordTopLevelError = false;
                  caretAtEndOrOnRightWhiteSpace = false;
               }
               else {
                  keywordTopLevelError = keywordApplNode.getChildren().get(1)
                        .getType() == NodeTypes.ERROR_NODE;
                  // Check for offset, because after last charater is not a
                  // valid offset
                  caretAtEndOrOnRightWhiteSpace = !keywordApplNode
                        .containsOffset(caretPosition);
               }
               // Caret is not allowed to be on the keyword itself and not at
               // the end of the keyword (or on whitespace) if the keywrod does
               // not contains a toplevel error (e.g. missing semicolon)
               if (!caretOnKeyword
                     && (!caretAtEndOrOnRightWhiteSpace || keywordTopLevelError)) {

                  // Get the keyword from the node and get result of
                  // autoproposals
                  final IKeyword activeKeyword = ((IKeywordNode) keywordApplNode
                        .getChildren().get(0)).getKeyword();
                  System.out.println("activeKeyword == " + activeKeyword);

                  final IKeywordAutoProposer proposer = activeKeyword
                        .createAutoProposer();
                  if (proposer != null) {

                     result.addAll(proposer.createAutoProposals(
                           keywordApplNode, javaContext));
                  }
               }
               else {

                  return this.getFallback(javaContext);
               }
            }
            else {
               System.out.println("no activeKeyword");
               return this.getFallback(javaContext);
            }

            return result;
         }
         // Fallback Method to display all JML Keyword-Proposals, if
         // no active Keyword was discovered.
         System.out.println("no parseResult");
         return this.getFallback(javaContext);
      }
      return result;

   }

   private List<ICompletionProposal> getFallback(
         final JavaContentAssistInvocationContext javaContext) {
      System.out.println("fallback");
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
