package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;

public class StoreRefKeywordProposer implements IKeywordAutoProposer {

   @Override
   public List<ICompletionProposal> createAutoProposals(final IASTNode node,
         final JavaContentAssistInvocationContext context) {
      final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();

      final IASTNode nodeAtPos = node;

      final CompilationUnit cu;
      if (context.getCompilationUnit() instanceof CompilationUnit) {
         cu = (CompilationUnit) context.getCompilationUnit();
      }
      else {
         // TODO make eclipse explode
         cu = null;
      }
      // Keyword APPL or error Node
      final IASTNode tmpNode = nodeAtPos.getChildren().get(1);
      // empty KeywordContent
      if (tmpNode.getChildren().isEmpty()) {
         result.addAll(new JMLStoreRefProposer(context)
               .propose(cu, null, false));
         return result;
      }
      IASTNode content = tmpNode.getChildren().get(0);

      System.out.println("node: " + node.prettyPrintAST());
      System.out.println("content: " + content);

      if (content.getType() == NodeTypes.ERROR_NODE) {
         // Toplevel error node is for missing semicolon. Try get content of
         // error
         if (content.getChildren().size() == 1) {
            content = content.getChildren().get(0);
         }
      }

      // TODO NodeTypes.LIST?
      if (content.getType() == StoreRefNodeTypes.STORE_REF_LIST) {
         final IASTNode exprInOffset = Nodes.selectChildWithPosition(content
               .getChildren().get(0), context.getInvocationOffset() - 1);
         final boolean hasExpr = content.traverse(
               new INodeTraverser<Boolean>() {

                  @Override
                  public Boolean traverse(final IASTNode node,
                        final Boolean existing) {
                     if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME) {
                        return true;
                     }
                     return existing;
                  }
               }, false);

         result.addAll(new JMLStoreRefProposer(context).propose(cu,
               exprInOffset, hasExpr));
      }
      else if (content.getType() == NodeTypes.KEYWORD) {
         // TODO
         System.out.println("fertig..." + content);
      }
      else if (content.getType() == NodeTypes.ERROR_NODE) {
         // TODO
         System.out.println("error");
      }
      else {
         System.out.println("nothing... ");
      }
      return result;
   }

}
