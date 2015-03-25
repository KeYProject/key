package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;

/**
 * This class provides AutoProposals for StoreRefKeywords (like assignable and
 * accessible).
 *
 * @author Thomas Glaser
 *
 */
public class StoreRefKeywordProposer implements IKeywordAutoProposer {

   /**
    * defines, whether to propose final variables or not.
    */
   private final boolean proposeFinal;

   /**
    * standard and only constructor.
    *
    * @param proposeFinal
    *           whether to propose final variables or not
    */
   public StoreRefKeywordProposer(final boolean proposeFinal) {
      super();
      this.proposeFinal = proposeFinal;
   }

   @Override
   public List<ICompletionProposal> createAutoProposals(final IASTNode node,
         final JavaContentAssistInvocationContext context) {
      final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();

      final IASTNode nodeAtPos = node;

      if (this.isOffsetAfterSemicolon(node, context)) {
         return null;
      }

      // Keyword APPL or error Node
      final IASTNode tmpNode = nodeAtPos.getChildren().get(1);
      // empty KeywordContent
      if (tmpNode.getChildren().isEmpty()) {
         result.addAll(new JMLStoreRefProposer(context, this.proposeFinal)
         .propose(null, false));
         return result;
      }
      IASTNode content = tmpNode.getChildren().get(0);
      if (content.getType() == NodeTypes.ERROR_NODE) {
         // Toplevel error node is for missing semicolon. Try get content of
         // error
         if (content.getChildren().size() == 1) {
            content = content.getChildren().get(0);
         }
      }

      // if we have a storeRef Expression, propose something
      if (content.getType() == StoreRefNodeTypes.STORE_REF_LIST) {
         final IASTNode exprInOffset = Nodes.selectChildWithPosition(content
               .getChildren().get(0), context.getInvocationOffset() - 1);
         final boolean hasExpr = content.traverse(
               new INodeTraverser<Boolean>() {
                  @Override
                  public Boolean traverse(final IASTNode node,
                        final Boolean existing) {
                     // added containsOffset, because i want to complete
                     // parameters and keywords as well
                     if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME
                           && !node.containsOffset(context
                                 .getInvocationOffset() - 1)) {
                        return true;
                     }
                     return existing;
                  }
               }, false);

         result.addAll(new JMLStoreRefProposer(context, this.proposeFinal)
         .propose(exprInOffset, hasExpr));
      }
      return result;
   }

   /**
    * if we want to propose something right after the closing ; we want to
    * propose TopLevelKeywords. this methods checks where the autoCompletion is
    * called.
    *
    * @param node
    *           the parsed JML
    * @param context
    *           the InvocationContext
    * @return true, if the autoCompletion is called after the closing ;, false
    *         if not.
    */
   private boolean isOffsetAfterSemicolon(final IASTNode node,
         final JavaContentAssistInvocationContext context) {
      // Check whether offset is after a closing semicolon
      final int invocationOffset = context.getInvocationOffset();
      if (invocationOffset >= node.getEndOffset()) {
         // Cursor after last character (invocationoffset inclusive,
         // node.getEndOffset exlusive, therfore >= )
         try {
            // If last char of the node is ; do not make proposals but requries
            // toplevel keywords
            if (context.getDocument().getChar(node.getEndOffset() - 1) == ';') {
               return true;
            }
         }
         catch (final BadLocationException e) {
            return true;
         }
      }
      return false;
   }

}
