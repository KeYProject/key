package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.internal.core.CompilationUnit;
import org.eclipse.jdt.internal.ui.viewsupport.BindingLabelProvider;
import org.eclipse.jdt.ui.text.java.JavaContentAssistInvocationContext;
import org.eclipse.jface.text.contentassist.CompletionProposal;
import org.eclipse.jface.text.contentassist.ICompletionProposal;
import org.eclipse.swt.graphics.Image;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLJavaVisibleFieldsComputer;
import org.key_project.jmlediting.core.utilities.MethodDeclarationFinder;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.jmlediting.ui.completion.JMLCompletionProposalComputer;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * The StoreRefProposer computes the AutoCompletion for StoreRefKeywords.
 * <ul>
 * <li>Visible Fields</li>
 * <li>Method Parameters</li>
 * </ul>
 *
 * @author Thomas Glaser
 *
 */
@SuppressWarnings("restriction")
public class JMLStoreRefProposer {
   /**
    * the invocationContext the AutoCompletion is called from.
    */
   private final JavaContentAssistInvocationContext context;
   /**
    * The TypeBinding the AutoCompletion is called in.
    */
   private ITypeBinding declaringType;
   /**
    * the computed List of MethodParameters catched from the AST.
    */
   private final HashMap<Integer, MethodDeclaration> parameterMap = new HashMap<Integer, MethodDeclaration>();

   /**
    * the CompilationUnit to get the AST from.
    */
   private final ICompilationUnit cu;

   /**
    * does the keyword wants to get final variables proposed.
    */
   private final boolean proposeFinal;

   /**
    * the only Constructor to instantiate the JMLStoreRefProposer.
    *
    * @param context
    *           The context the AutoCompletion is called from
    * @param proposeFinal
    *           let the keyword decide whether to propose final variables
    *
    */
   public JMLStoreRefProposer(final JavaContentAssistInvocationContext context,
         final boolean proposeFinal) {
      super();
      this.context = context;
      this.proposeFinal = proposeFinal;
      if (context.getCompilationUnit() instanceof CompilationUnit) {
         this.cu = context.getCompilationUnit();
      }
      else {
         this.cu = null;
      }
   }

   /**
    * proposes the AutoCompletion for StoreRefKeywords.
    *
    * @param expr
    *           the parsed JML to compute the AutoCompletion for
    * @param hasOtherExpressions
    *           is this the first Expression for this specific StoreRefKeyword
    * @return the computed CompletionProposals, empty List if none are found
    */
   public Collection<ICompletionProposal> propose(final IASTNode expr,
         final boolean hasOtherExpressions) {
      final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
      final org.eclipse.jdt.core.dom.CompilationUnit ast = (org.eclipse.jdt.core.dom.CompilationUnit) JDTUtil.parse(this.cu);

      // find all TypeDeclarations
      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      ast.accept(finder);

      final List<TypeDeclaration> decls = finder.getDecls();
      TypeDeclaration activeTypeDecl = null;
      // find the activeTypeDeclaration to compute the completion.
      for (final TypeDeclaration decl : decls) {
         final int end = decl.getStartPosition() + decl.getLength();
         // ignore all types after the invocationOffset, one may call
         // AutoCompletion in the middle of some word or sequence
         if (decl.getStartPosition() <= this.context.getInvocationOffset()
               && end >= this.context.getInvocationOffset()) {
            activeTypeDecl = decl;
         }
      }

      // compute all TypeBinding needed to resolve visibility of variables
      final ITypeBinding activeType;
      if (activeTypeDecl != null) {
         activeType = activeTypeDecl.resolveBinding();
      }
      else {
         activeType = null;
      }
      this.declaringType = activeType;
      final IASTNode node;
      final List<IASTNode> restNodes;
      final boolean allowKeywords;
      allowKeywords = !hasOtherExpressions;
      if (expr == null) {
         final int invocationOffset = this.context.getInvocationOffset();
         node = Nodes.createNode(StoreRefNodeTypes.STORE_REF_NAME,
               Nodes.createString(invocationOffset, invocationOffset, ""));
         restNodes = Collections.<IASTNode> emptyList();
      }
      else {
         node = expr.getChildren().get(0);
         restNodes = expr.getChildren().get(1).getChildren();
      }

      // find all methods to get all MethodParameters
      final MethodDeclarationFinder methodFinder = new MethodDeclarationFinder();
      ast.accept(methodFinder);
      for (final MethodDeclaration decl : methodFinder.getDecls()) {
         final int firstLeadingComment = ast.firstLeadingCommentIndex(decl);
         if (firstLeadingComment == -1) {
            continue;
         }
         final int commentBeginOffset = ((Comment) ast.getCommentList().get(
               firstLeadingComment)).getStartPosition();
         this.parameterMap.put(commentBeginOffset, decl);
      }

      // compute the prefix the AutoCompletion has to handle
      final String prefix = JMLCompletionUtil.computePrefix(this.context, node);

      // propose StoreRef specific keywords, when called at the beginning.
      if (allowKeywords) {
         result.addAll(JMLCompletionUtil.getKeywordProposals(this.context,
               prefix, JMLCompletionProposalComputer.getJMLImg(),
               StoreRefKeywordSort.INSTANCE));
      }

      // propose all (visible)fields
      if (activeType != null) {
         result.addAll(this.proposeStoreRefVariables(activeType, node,
               restNodes, false, allowKeywords, true));
      }

      // if we have no other Expressions, we can propose the Method parameters
      // -> only at the beginning of proposals;
      if (!hasOtherExpressions) {
         result.addAll(this.proposeMethodParameters(prefix));
      }

      // atm not implemented, but here API statements get resolved and
      // fields from them get proposed
      result.addAll(this.proposeStoreRefApiVariables(node, restNodes));

      Collections.sort(result, new Comparator<ICompletionProposal>() {
         @Override
         public int compare(final ICompletionProposal o1,
               final ICompletionProposal o2) {
            return o1.getDisplayString().compareTo(o2.getDisplayString());
         };
      });

      return result;
   }

   /**
    * propose methodParameters from the following method.
    *
    * @param prefix
    *           the prefix to compute the proposals for
    * @return all Method parameters matching the prefix, empty List of none
    *         matched
    */
   private Collection<? extends ICompletionProposal> proposeMethodParameters(
         final String prefix) {
      final Collection<ICompletionProposal> result = new ArrayList<ICompletionProposal>();

      final MethodDeclaration method = this.getMethodDeclaration();
      if (method != null && method.parameters() != null) {
         @SuppressWarnings("unchecked")
         final List<SingleVariableDeclaration> methodParams = method
         .parameters();
         final int replacementOffset = this.context.getInvocationOffset()
               - prefix.length();
         final int prefixLength = prefix.length();
         // check all VariableDeclarations to match the prefix
         for (final SingleVariableDeclaration param : methodParams) {
            final IVariableBinding varBind = param.resolveBinding();
            final Image image = BindingLabelProvider.getBindingImageDescriptor(
                  varBind, 0).createImage();
            final String replacementString = param.getName().toString();
            if (replacementString.startsWith(prefix)
                  && this.checkFinalVisible(varBind, method)) {
               final int cursorPosition = replacementString.length();
               result.add(new CompletionProposal(replacementString,
                     replacementOffset, prefixLength, cursorPosition, image,
                     replacementString, null, null));
            }
         }
      }

      return result;
   }

   /**
    * helper method to get the MethodDeclaration for the JML-Comment the
    * AutoCompletion is called in.
    *
    * @return the corresponding MethodDeclaration according to InvocationOffset
    */
   private MethodDeclaration getMethodDeclaration() {
      final int offset = this.context.getInvocationOffset();

      final CommentRange range = CommentLocator.getJMLComment(this.context.getDocument(), offset);

      return this.parameterMap.get(range.getBeginOffset());
   }

   /**
    * helper Method to resolve the type of a Method Parameter to propose further
    * variables.
    *
    * @param fieldName
    *           the name of the variable
    * @return the ITypeBinding for the corresponding variable-type
    */
   private ITypeBinding getMethodParameterTypeForName(final String fieldName) {
      final MethodDeclaration method = this.getMethodDeclaration();
      if (method == null) {
         return null;
      }
      @SuppressWarnings("unchecked")
      final List<SingleVariableDeclaration> methodParams = method.parameters();
      if (methodParams == null) {
         return null;
      }
      for (final SingleVariableDeclaration varDecl : methodParams) {
         final IVariableBinding varBind = varDecl.resolveBinding();
         if (varBind.getName().equals(fieldName)
               && this.checkFinalVisible(varBind, method)) {
            return varBind.getType();
         }
      }
      return null;
   }

   /**
    * (may be extracted some time). Propose all visible Variables for StoreRef
    * AutoCompletion
    *
    *
    * @param activeType
    *           the ITypeBinding to look in
    * @param node
    *           the parsed JML
    * @param restNodes
    *           the JML following the current Type
    * @param allowAsteric
    *           whether to allow the asteric as a proposal
    * @param allowKeywords
    *           whether to allow keywords as a proposal
    * @param withProtectedOrInline
    *           propose protected or inline variables
    * @return the list of variables to propose;
    */
   private List<ICompletionProposal> proposeStoreRefVariables(
         final ITypeBinding activeType, final IASTNode node,
         final List<IASTNode> restNodes, final boolean allowAsteric,
         final boolean allowKeywords, final boolean withProtectedOrInline) {
      final int type = node.getType();

      // cut the prefix to the cursor position
      final String prefix = JMLCompletionUtil.computePrefix(this.context, node);

      final JMLJavaVisibleFieldsComputer resolver = new JMLJavaVisibleFieldsComputer(
            this.declaringType);

      // if prefix != null the cursor is in or before the currentNode ->
      // compute the proposals
      if (restNodes.isEmpty() || prefix != null) {
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
                  && this.checkFinalVisible(varBind, null)) {
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
         if (type == StoreRefNodeTypes.STORE_REF_NAME
               || type == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
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
            // check for Method parameters
            if (nextType == null) {
               nextType = this.getMethodParameterTypeForName(name);
            }

            // check for fields
            if (nextType == null) {
               nextType = resolver.getTypeForName(activeType, name);
            }

            if (nextType == null) {
               return Collections.emptyList();
            }
            return this.proposeStoreRefVariables(nextType, restNodes.get(0),
                  restNodes.subList(1, restNodes.size()), true, false, false);
         }
         return Collections.emptyList();
      }
   }

   /**
    * not implemented yet.
    *
    * @param node
    *           current parsed JML
    * @param restNodes
    *           following JML
    * @return proposals for API-Variables
    */
   private Collection<ICompletionProposal> proposeStoreRefApiVariables(
         final IASTNode node, final List<IASTNode> restNodes) {
      return Collections.emptyList();
   }

   /**
    * check whether a final variable is visible to propose.
    *
    * @param varBind
    *           the variable to check visibility for
    * @param method
    *           the
    * @return whether final variables should be visible or not
    */
   private boolean checkFinalVisible(final IVariableBinding varBind,
         final MethodDeclaration method) {
      return (varBind.getModifiers() & Modifier.FINAL) == 0
            || this.proposeFinal || (method != null && method.isConstructor());
   }
}