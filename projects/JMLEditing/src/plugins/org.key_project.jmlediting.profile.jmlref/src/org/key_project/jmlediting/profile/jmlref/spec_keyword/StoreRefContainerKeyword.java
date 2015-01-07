package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import java.util.List;

import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordContentParser;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

/**
 * A keyword, which contains storage references as content.
 *
 * @author Moritz Lichter
 *
 */
public abstract class StoreRefContainerKeyword extends
      AbstractGenericSpecificationKeyword {

   /**
    * Creates a new {@link StoreRefContainerKeyword}.
    *
    * @param keyword
    *           the keyword
    * @param keywords
    *           optional other keywords
    */
   public StoreRefContainerKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordParser createParser() {
      return new StoreRefKeywordContentParser(true);
   }

   @Override
   @SuppressWarnings("restriction")
   public List<ICompletionProposal> createAutoProposals(final IASTNode node,
         final JavaContentAssistInvocationContext context) {

      final IASTNode tmpNode = Nodes.getDepthMostNodeWithPosition(
            context.getInvocationOffset(), node);

      final int begin = tmpNode.getStartOffset();
      final int end = context.getInvocationOffset();

      System.out.println("Node: " + tmpNode);
      System.out.println("begin: " + begin + "; end: " + end);

      final String prefix = context.getDocument().get().substring(begin, end);
      System.out.println("got Prefix: " + prefix);

      final CompilationUnit result = (CompilationUnit) context
            .getCompilationUnit();
      try {
         for (final IJavaElement element : result.getChildren()) {
            if (element.getElementType() == IJavaElement.TYPE) {
               final IType typeElement = (IType) element;

               for (final IField field : typeElement.getFields()) {
                  System.out.println("---");
                  System.out.println(field);
                  System.out.println("---");
                  System.out.println("elementName: " + field.getElementName());
                  System.out.println("---");
                  System.out.println("source: " + field.getSource());
                  System.out.println("---");
                  System.out.println("isResolved: " + field.isResolved());
                  System.out.println("---");
                  System.out.println("path: " + field.getPath());
               }
            }
         }
      }

      catch (final JavaModelException e) {
         // TODO Auto-generated catch block
         e.printStackTrace();
      }

      return JMLCompletionUtil.getKeywordProposals(context, prefix, null,
            IStoreRefKeyword.class);
   }
}
