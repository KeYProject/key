package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTVisitor;
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
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
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

   private static class TypeDeclarationFinder extends ASTVisitor {
      private final List<TypeDeclaration> decls = new ArrayList<TypeDeclaration>();

      public List<TypeDeclaration> getDecls() {
         return this.decls;
      }

      @Override
      public boolean visit(final TypeDeclaration node) {
         this.decls.add(node);
         return super.visit(node);
      }
   };

   @SuppressWarnings("restriction")
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
      if (tmpNode.getChildren().isEmpty()) {
         result.addAll(new Proposer(context).propose(cu, null));
         result.addAll(JMLCompletionUtil.getKeywordProposals(context, null,
               null, IStoreRefKeyword.class));
         return result;
      }
      final IASTNode content = tmpNode.getChildren().get(0);

      if (content.getType() == StoreRefNodeTypes.STORE_REF_LIST) {
         // System.out.println(content);
         final IASTNode exprInOffset = Nodes.selectChildWithPosition(content,
               context.getInvocationOffset() - 1);
         // TODO checl exprInOffset == null
         final List<IASTNode> list = exprInOffset.getChildren();
         result.addAll(new Proposer(context).propose(cu, list));
      }
      else if (content.getType() == NodeTypes.KEYWORD) {
         // TODO
         System.out.println("fertig..." + content);
      }
      else if (content.getType() == NodeTypes.ERROR_NODE) {
         // TODO
         System.out.println("error");
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
            final CompilationUnit cu, final List<IASTNode> list) {
         final org.eclipse.jdt.core.dom.CompilationUnit ast = SharedASTProvider
               .getAST(cu, SharedASTProvider.WAIT_YES, null);

         final TypeDeclarationFinder finder = new TypeDeclarationFinder();
         ast.accept(finder);
         final List<TypeDeclaration> decls = finder.getDecls();
         final TypeDeclaration topDecl = decls.get(0);
         if (list == null) {
            final int invocationOffset = this.context.getInvocationOffset();
            System.out.println("list == null");
            return this.propose(topDecl.resolveBinding(), Nodes.createNode(
                  StoreRefNodeTypes.STORE_REF_NAME,
                  Nodes.createString(invocationOffset, invocationOffset, "")),
                  Collections.<IASTNode> emptyList(), false);
         }
         System.out.println("");
         return this.propose(topDecl.resolveBinding(), list.get(0)
               .getChildren().get(0), list.get(0).getChildren().get(1)
               .getChildren(), false);
      }

      private List<ICompletionProposal> propose(final ITypeBinding activeType,
            final IASTNode node, final List<IASTNode> restNodes,
            final boolean allowAsteric) {
         final int type = node.getType();
         // any prefix?
         if (restNodes.isEmpty()) {
            final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
            final IVariableBinding[] vars = activeType.getDeclaredFields();
            final String prefix = ((IStringNode) node.getChildren().get(0))
                  .getString();
            final int replacementOffset = this.context.getInvocationOffset()
                  - prefix.length();
            final int prefixLength = prefix.length();
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
         // we have a prefix
         else {
            ITypeBinding nextType = null;
            System.out.println(node + " @ "
                  + this.context.getInvocationOffset());
            if (!node.containsOffset(this.context.getInvocationOffset())) {
               // nur bis zum invooffset als prefix und auch innerhalb nur bis
               // zum invooffset
               // TODO final hier weiter machen
               return this.propose(activeType, node,
                     Collections.<IASTNode> emptyList(), true);
            }
            if (type == StoreRefNodeTypes.STORE_REF_NAME
                  || type == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
               System.out.println("in sore_ref_name[_suffix]");
               final String name = ((IStringNode) node.getChildren().get(0))
                     .getString();
               IVariableBinding foundBinding = null;
               for (final IVariableBinding varBind : activeType
                     .getDeclaredFields()) {
                  if (name.equals(varBind.getName())) {
                     foundBinding = varBind;
                     break;
                  }
               }
               if (foundBinding == null) {
                  System.out.println("foundBinding is null");
                  return Collections.emptyList();
               }
               nextType = foundBinding.getType();
            }
            return this.propose(nextType, restNodes.get(0),
                  restNodes.subList(1, restNodes.size()), true);
         }
      }
   }
}
