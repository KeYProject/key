package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import java.util.List;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordContentParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

public abstract class StoreRefContainerKeyword extends
AbstractGenericSpecificationKeyword {

   public StoreRefContainerKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordParser createParser() {
      return new StoreRefKeywordContentParser(true);
   }

   @Override
   public List<ICompletionProposal> createAutoProposals(final IASTNode node,
         final JavaContentAssistInvocationContext context) {

      final IASTNode tmpNode = this.getNodeForProposal(node);

      final int begin = tmpNode.getStartOffset();
      final int end = context.getInvocationOffset();

      final String prefix = context.getDocument().get().substring(begin, end);

      final char[] text = context.getDocument().get().toCharArray();

      final CompilationUnit result = (CompilationUnit) context
            .getCompilationUnit();

      try {
         for (final IJavaElement element : result.getChildren()) {
            System.out.println("------");
            if (element.getElementType() == IJavaElement.TYPE) {
               // TODO
            }
            System.out.println(element.getElementType() + ": " + element);
         }
      }
      catch (final JavaModelException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

      return JMLCompletionUtil.getKeywordProposals(context, prefix, null,
            IStoreRefKeyword.class);
   }

   private IASTNode getNodeForProposal(final IASTNode node) {
      IASTNode result = node;
      for (final IASTNode child : node.getChildren()) {
         if (child.getType() == StoreRefNodeTypes.STORE_REF_EXPR) {
            result = child;
            break;
         }
         else {
            result = this.getNodeForProposal(child);
         }
      }
      return result;
   }
}
