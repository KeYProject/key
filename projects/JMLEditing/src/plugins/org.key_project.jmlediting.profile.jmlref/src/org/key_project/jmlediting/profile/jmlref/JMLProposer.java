package org.key_project.jmlediting.profile.jmlref;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.ui.SharedASTProvider;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.utilities.JMLJavaResolver;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

@SuppressWarnings("restriction")
public class JMLProposer {
   private final JavaContentAssistInvocationContext context;

   public JMLProposer(final JavaContentAssistInvocationContext context) {
      super();
      this.context = context;
   }

   public Collection<? extends ICompletionProposal> proposeVariables(
         final CompilationUnit cu, final IASTNode expr,
         final boolean hasOtherExpressions) {
      final org.eclipse.jdt.core.dom.CompilationUnit ast = SharedASTProvider
            .getAST(cu, SharedASTProvider.WAIT_YES, null);

      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      ast.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(0);
      if (expr == null) {
         final int invocationOffset = this.context.getInvocationOffset();
         return this
               .proposeVariables(topDecl.resolveBinding(),
                     Nodes.createNode(StoreRefNodeTypes.STORE_REF_NAME,
                           Nodes.createString(invocationOffset,
                                 invocationOffset, "")), Collections
                           .<IASTNode> emptyList(), false,
                     !hasOtherExpressions, true);
      }

      System.out.println("expr: " + expr.prettyPrintAST());

      return this.proposeVariables(topDecl.resolveBinding(), expr.getChildren()
            .get(0), expr.getChildren().get(1).getChildren(), false, false,
            true);
   }

   private List<ICompletionProposal> proposeVariables(
         final ITypeBinding activeType, final IASTNode node,
         final List<IASTNode> restNodes, final boolean allowAsteric,
         final boolean allowKeywords, final boolean withProtectedOrInline) {
      final int type = node.getType();
      // any prefix?
      System.out.println("------------------------------------------------");
      System.out.println("node == " + node);
      System.out.println("restNodes == " + restNodes);

      // cut the prefix to the cursor position
      String prefix = null;
      if (node.containsOffset(this.context.getInvocationOffset() - 1)) {
         final IASTNode wordNode = Nodes.getDepthMostNodeWithPosition(
               this.context.getInvocationOffset() - 1, node);
         // the cursor is in the current Node => substring
         System.out.println("im offset ");
         prefix = this.context
               .getDocument()
               .get()
               .substring(wordNode.getStartOffset(),
                     this.context.getInvocationOffset());
      }
      else if (node.getStartOffset() >= this.context.getInvocationOffset()) {
         // the node is after the cursor => empty prefix and break the
         // recursion
         System.out.println("zu spät...");
         prefix = "";
      }

      final JMLJavaResolver resolver = new JMLJavaResolver(activeType);

      // if prefix != null the cursor is in or before the currentNode ->
      // compute the proposals
      if (restNodes.isEmpty() || prefix != null) {
         final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
         final List<IVariableBinding> vars = resolver
               .getAllVisibleVariableBindings();
         if (prefix == null) {
            prefix = ((IStringNode) node.getChildren().get(0)).getString();
         }
         // ignore . as a prefix
         if (prefix.equals(".")) {
            prefix = "";
         }
         // don't accept * as a prefix
         else if (prefix.equals("*")) {
            return result;
         }
         // TODO check for ArrayIndices
         System.out.println("prefix == " + prefix);
         final int replacementOffset = this.context.getInvocationOffset()
               - prefix.length();
         final int prefixLength = prefix.length();
         if (prefix.isEmpty() && allowKeywords) {
            result.addAll(JMLCompletionUtil.getKeywordProposals(this.context,
                  null, null, IStoreRefKeyword.class));
         }
         if (prefix.isEmpty() && allowAsteric) {
            final String replacementString = "*";
            final int cursorPosition = replacementString.length();
            result.add(new CompletionProposal(replacementString,
                  replacementOffset, prefixLength, cursorPosition));
         }
         for (final IVariableBinding varBind : vars) {
            if (varBind.getName().startsWith(prefix)) {
               final String replacementString = varBind.getName();
               final int cursorPosition = replacementString.length();
               result.add(new CompletionProposal(replacementString,
                     replacementOffset, prefixLength, cursorPosition));
            }
         }

         return result;
      }
      else {
         if (type == StoreRefNodeTypes.STORE_REF_NAME
               || type == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
            System.out.println("in store_ref_name[_suffix]");
            final String name = ((IStringNode) node.getChildren().get(0))
                  .getString();

            final ITypeBinding nextType = resolver.getTypeForName(name);
            if (nextType == null) {
               return Collections.emptyList();
            }
            return this.proposeVariables(nextType, restNodes.get(0),
                  restNodes.subList(1, restNodes.size()), true, false, false);
         }
         return Collections.emptyList();
      }
   }
}