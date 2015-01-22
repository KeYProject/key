package org.key_project.jmlediting.profile.jmlref.spec_keyword;

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
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.utilities.JMLJavaResolver;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.IStoreRefKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordContentParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

/**
 * A keyword, which contains storage references as content.
 *
 * @author Moritz Lichter
 *
 */
@SuppressWarnings("restriction")
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
   public List<ICompletionProposal> createAutoProposals(final IASTNode node,
         final JavaContentAssistInvocationContext context) {
      final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();

      final IASTNode nodeAtPos = Nodes.getNodeAtPosition(node,
            context.getInvocationOffset() - 1, NodeTypes.KEYWORD_APPL);

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
         result.addAll(new Proposer(context).propose(cu, null, false));
         return result;
      }
      final IASTNode content = tmpNode.getChildren().get(0);

      System.out.println("node: " + node.prettyPrintAST());
      System.out.println("content: " + content);

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

         result.addAll(new Proposer(context).propose(cu, exprInOffset, hasExpr));
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

   private static class Proposer {
      private final JavaContentAssistInvocationContext context;

      public Proposer(final JavaContentAssistInvocationContext context) {
         super();
         this.context = context;
      }

      private Collection<? extends ICompletionProposal> propose(
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
            return this.propose(topDecl.resolveBinding(), Nodes.createNode(
                  StoreRefNodeTypes.STORE_REF_NAME,
                  Nodes.createString(invocationOffset, invocationOffset, "")),
                  Collections.<IASTNode> emptyList(), false,
                  !hasOtherExpressions, true);
         }

         System.out.println("expr: " + expr.prettyPrintAST());

         return this.propose(topDecl.resolveBinding(), expr.getChildren()
               .get(0), expr.getChildren().get(1).getChildren(), false, false,
               true);
      }

      private List<ICompletionProposal> propose(final ITypeBinding activeType,
            final IASTNode node, final List<IASTNode> restNodes,
            final boolean allowAsteric, final boolean allowKeywords,
            final boolean withProtectedOrInline) {
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
               result.addAll(JMLCompletionUtil.getKeywordProposals(
                     this.context, null, null, IStoreRefKeyword.class));
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
               return this
                     .propose(nextType, restNodes.get(0),
                           restNodes.subList(1, restNodes.size()), true, false,
                           false);
            }
            return Collections.emptyList();
         }
      }
   }
}
