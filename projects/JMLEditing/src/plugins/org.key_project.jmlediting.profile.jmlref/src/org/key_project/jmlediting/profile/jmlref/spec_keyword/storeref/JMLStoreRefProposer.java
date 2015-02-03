package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.internal.ui.viewsupport.BindingLabelProvider;
import org.eclipse.jdt.ui.SharedASTProvider;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.utilities.JMLJavaVisibleFieldsComputer;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.jmlediting.ui.completion.JMLCompletionProposalComputer;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

@SuppressWarnings("restriction")
public class JMLStoreRefProposer {
   private final JavaContentAssistInvocationContext context;
   private ITypeBinding declaringType;

   public JMLStoreRefProposer(final JavaContentAssistInvocationContext context) {
      super();
      this.context = context;
   }

   public Collection<ICompletionProposal> propose(final CompilationUnit cu,
         final IASTNode expr, final boolean hasOtherExpressions) {
      final Collection<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
      final org.eclipse.jdt.core.dom.CompilationUnit ast = SharedASTProvider
            .getAST(cu, SharedASTProvider.WAIT_YES, null);

      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      ast.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(0);
      TypeDeclaration activeTypeDecl = null;
      for (final TypeDeclaration decl : decls) {
         final int end = decl.getStartPosition() + decl.getLength();
         if (decl.getStartPosition() <= this.context.getInvocationOffset()
               && end >= this.context.getInvocationOffset()) {
            activeTypeDecl = decl;
         }
      }

      final ITypeBinding activeType = activeTypeDecl.resolveBinding();
      this.declaringType = topDecl.resolveBinding();
      System.out.println("declaring: " + this.declaringType.getName());
      System.out.println("active: " + activeType.getName());
      System.out.println("activeIsNested?" + activeType.isNested());
      final IASTNode node;
      final List<IASTNode> restNodes;
      final boolean allowKeywords;
      if (expr == null) {
         final int invocationOffset = this.context.getInvocationOffset();
         node = Nodes.createNode(StoreRefNodeTypes.STORE_REF_NAME,
               Nodes.createString(invocationOffset, invocationOffset, ""));
         restNodes = Collections.<IASTNode> emptyList();
         allowKeywords = !hasOtherExpressions;
      }
      else {
         System.out.println("expr: " + expr.prettyPrintAST());
         node = expr.getChildren().get(0);
         restNodes = expr.getChildren().get(1).getChildren();
         allowKeywords = false;
      }

      final String prefix = JMLCompletionUtil.computePrefix(this.context, node);

      // TODO check for ArrayIndices
      if (prefix != null && prefix.isEmpty() && allowKeywords) {
         result.addAll(JMLCompletionUtil.getKeywordProposals(this.context,
               null, JMLCompletionProposalComputer.getJMLImg(),
               IStoreRefKeyword.class));
      }

      result.addAll(this.proposeStoreRefVariables(activeType, node, restNodes,
            false, allowKeywords, true));

      result.addAll(this.proposeStoreRefApiVariables(node, restNodes));

      return result;
   }

   private List<ICompletionProposal> proposeStoreRefVariables(
         final ITypeBinding activeType, final IASTNode node,
         final List<IASTNode> restNodes, final boolean allowAsteric,
         final boolean allowKeywords, final boolean withProtectedOrInline) {
      final int type = node.getType();

      System.out.println("------------------------------------------------");
      System.out.println("node == " + node);
      System.out.println("restNodes == " + restNodes);

      // cut the prefix to the cursor position
      final String prefix = JMLCompletionUtil.computePrefix(this.context, node);

      final JMLJavaVisibleFieldsComputer resolver = new JMLJavaVisibleFieldsComputer(
            this.declaringType);

      // if prefix != null the cursor is in or before the currentNode ->
      // compute the proposals
      if (restNodes.isEmpty() || prefix != null) {
         System.out.println("MAKING PROPOSALS");
         final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
         // don't accept * as a prefix
         if (prefix.equals("*")) {
            return result;
         }

         final List<IVariableBinding> vars = resolver
               .getAllVisibleFields(activeType);

         final int replacementOffset = this.context.getInvocationOffset()
               - prefix.length();
         final int prefixLength = prefix.length();

         if (prefix.isEmpty() && allowAsteric && !activeType.isPrimitive()) {
            final String replacementString = "*";
            final int cursorPosition = replacementString.length();
            result.add(new CompletionProposal(replacementString,
                  replacementOffset, prefixLength, cursorPosition,
                  JMLCompletionProposalComputer.getJMLImg(), replacementString,
                  null, null));
         }
         for (final IVariableBinding varBind : vars) {
            if (varBind.getName().startsWith(prefix)
                  && ((varBind.getModifiers() & Modifier.FINAL) == 0)) {
               final String replacementString = varBind.getName();
               final int cursorPosition = replacementString.length();

               final Image image = BindingLabelProvider
                     .getBindingImageDescriptor(varBind, 0).createImage();
               result.add(new CompletionProposal(replacementString,
                     replacementOffset, prefixLength, cursorPosition, image,
                     replacementString, null, null));
            }
         }

         return result;
      }
      else {
         System.out.println("GO DEEPER (with Type: "
               + NodeTypes.getTypeName(type) + ")");
         if (type == StoreRefNodeTypes.STORE_REF_NAME
               || type == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
            System.out.println("in store_ref_name[_suffix]");
            final String name = ((IStringNode) node.getChildren().get(0))
                  .getString();

            ITypeBinding nextType = null;
            // Handle this and super
            // this is not correct completely because the implementation
            // allows this as a field access which is not correct
            // this/super is allowed as an initial identifier and after
            // a trype of the current or an enclosing class which is not handled
            // currently
            if (activeType == this.declaringType) {
               if (name.equals("this")) {
                  nextType = activeType;
               }
               else if (name.equals("super")) {
                  nextType = activeType.getSuperclass();
               }
            }
            if (nextType == null) {
               System.out.println("searchingType for: " + name);
               nextType = resolver.getTypeForName(activeType, name);
            }

            if (nextType == null) {
               System.out.println("AAAAaaahhhhh, nextType is null!");
               return Collections.emptyList();
            }
            return this.proposeStoreRefVariables(nextType, restNodes.get(0),
                  restNodes.subList(1, restNodes.size()), true, false, false);
         }
         return Collections.emptyList();
      }
   }

   private Collection<ICompletionProposal> proposeStoreRefApiVariables(
         final IASTNode node, final List<IASTNode> restNodes) {
      final Collection<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
      // TODO
      return result;
   }
}