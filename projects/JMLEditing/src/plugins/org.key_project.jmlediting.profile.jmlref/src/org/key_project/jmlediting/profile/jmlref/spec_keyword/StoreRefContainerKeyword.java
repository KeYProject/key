package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.dom.AST;
import org.eclipse.jdt.core.dom.ASTParser;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
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

      // We want to use java6
      @SuppressWarnings("deprecation")
      final ASTParser parser = ASTParser.newParser(AST.JLS3);
      parser.setProject(context.getProject());
      parser.setSource(context.getDocument().get().toCharArray());
      parser.setKind(ASTParser.K_COMPILATION_UNIT);
      final Map<String, String> options = JavaCore.getOptions();
      JavaCore.setComplianceOptions(JavaCore.VERSION_1_6, options);
      parser.setCompilerOptions(options);

      final CompilationUnit result = (CompilationUnit) parser.createAST(null);

      final List<Integer> variables = new ArrayList<Integer>();

      result.accept(new ASTVisitor() {
         @Override
         public boolean visit(final VariableDeclarationFragment node) {
            System.out.println("found declaration: " + node);
            variables.add(node.getStartPosition());
            return super.visit(node);
         }
      });

      for (final Integer pos : variables) {
         System.out.println("ElementAt(" + pos + "): ");
      }

      return JMLCompletionUtil.getProposals(context, null, null,
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
