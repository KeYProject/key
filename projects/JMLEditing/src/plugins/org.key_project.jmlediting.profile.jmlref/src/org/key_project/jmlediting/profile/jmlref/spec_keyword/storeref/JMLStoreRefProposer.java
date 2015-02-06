package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.eclipse.jdt.core.dom.ASTParser;
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
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLJavaVisibleFieldsComputer;
import org.key_project.jmlediting.core.utilities.MethodDeclarationFinder;
import org.key_project.jmlediting.core.utilities.MethodParameter;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.jmlediting.ui.completion.JMLCompletionProposalComputer;
import org.key_project.jmlediting.ui.util.JMLCompletionUtil;

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
   private final List<MethodParameter> parameterList = new ArrayList<MethodParameter>();

   /**
    * the CompilationUnit to get the AST from.
    */
   private final CompilationUnit cu;

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
         this.cu = (CompilationUnit) context.getCompilationUnit();
      }
      else {
         // TODO make eclipse explode
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
   @SuppressWarnings("unchecked")
   public Collection<ICompletionProposal> propose(final IASTNode expr,
         final boolean hasOtherExpressions) {
      final List<ICompletionProposal> result = new ArrayList<ICompletionProposal>();
      final org.eclipse.jdt.core.dom.CompilationUnit ast;
      final ASTParser parser = ASTParser
            .newParser(ASTParser.K_COMPILATION_UNIT);
      parser.setKind(ASTParser.K_COMPILATION_UNIT);
      parser.setSource(this.cu);
      parser.setResolveBindings(true);
      ast = (org.eclipse.jdt.core.dom.CompilationUnit) parser.createAST(null);

      // find all TypeDeclarations
      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      ast.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(0);
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
      final ITypeBinding activeType = activeTypeDecl.resolveBinding();
      this.declaringType = topDecl.resolveBinding();
      System.out.println("declaring: " + this.declaringType.getName());
      System.out.println("active: " + activeType.getName());
      System.out.println("activeIsNested?" + activeType.isNested());
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
         System.out.println("expr: " + expr.prettyPrintAST());
         node = expr.getChildren().get(0);
         restNodes = expr.getChildren().get(1).getChildren();
      }

      // find all methods to get all MethodParameters
      final MethodDeclarationFinder methodFinder = new MethodDeclarationFinder();
      ast.accept(methodFinder);

      for (final MethodDeclaration decl : methodFinder.getDecls()) {
         this.parameterList.add(new MethodParameter(decl.getStartPosition(),
               decl.parameters()));
      }

      // compute the prefix the AutoCompletion has to handle
      final String prefix = JMLCompletionUtil.computePrefix(this.context, node);

      // TODO check for ArrayIndices
      System.out.println("allowKeywords == " + allowKeywords);
      // propose StoreRef specific keywords, when called at the beginning.
      if (allowKeywords) {
         result.addAll(JMLCompletionUtil.getKeywordProposals(this.context,
               prefix, JMLCompletionProposalComputer.getJMLImg(),
               IStoreRefKeyword.class));
      }

      // propose all (visible)fields
      result.addAll(this.proposeStoreRefVariables(activeType, node, restNodes,
            false, allowKeywords, true));

      // if we have no other Expressions, we can propose the Method parameters
      // -> only at the beginning of proposals;
      if (!hasOtherExpressions) {
         result.addAll(this.proposeMethodParameters(prefix));
      }

      // TODO atm not implemented, but here API statements get resolved and
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

      final MethodParameter methodParams = this.getMethodParams();
      if (methodParams != null) {
         final int replacementOffset = this.context.getInvocationOffset()
               - prefix.length();
         final int prefixLength = prefix.length();
         System.out.println("Prefix: " + prefix);
         // check all VariableDeclarations to match the prefix
         for (final SingleVariableDeclaration param : methodParams
               .getParameters()) {
            final IVariableBinding varBind = param.resolveBinding();
            final Image image = BindingLabelProvider.getBindingImageDescriptor(
                  varBind, 0).createImage();
            final String replacementString = param.getName().toString();
            if (replacementString.startsWith(prefix)
                  && ((varBind.getModifiers() & Modifier.FINAL) == 0 || this.proposeFinal)) {
               final int cursorPosition = replacementString.length();
               result.add(new CompletionProposal(replacementString,
                     replacementOffset, prefixLength, cursorPosition, image,
                     replacementString, null, null));
               System.out.println("added: " + replacementString);
            }
         }
      }

      return result;
   }

   private MethodParameter getMethodParams() {
      final int offset = this.context.getInvocationOffset();

      final CommentLocator locator = new CommentLocator(
            this.context.getDocument());

      final CommentRange range = locator.getJMLComment(offset);
      System.out.println("commentRange: " + range.getBeginOffset() + "-"
            + range.getEndOffset());

      final String content = this.context.getDocument().get();

      MethodParameter result = null;

      // search for the Methodparameters
      for (final MethodParameter methodParams : this.parameterList) {
         // continue if comment is after the method -> no checking needed
         if (range.getEndOffset() > methodParams.getStartOffset()) {
            System.out.println("outOfRange: " + methodParams.getStartOffset());
            continue;
         }
         boolean setResult = true;
         // check all following characters to be either whitespace or eol, or to
         // be in comment. Else the JMLComment does not belong to this method
         for (int i = range.getEndOffset(); i < methodParams.getStartOffset() - 1; i++) {
            final char toBeChecked = content.charAt(i);
            System.out.println("checking chat at " + i + ": \'" + toBeChecked
                  + "\'");
            if (toBeChecked == ' ' || toBeChecked == '\n'
                  || toBeChecked == '\r') {
               System.out.println("\twhitespace/eol");
               continue;
            }
            else if (locator.getCommentOfOffset(i) != null) {
               System.out.println("\tinComment");
               continue;
            }
            System.out.println("noAddParams...");
            setResult = false;
            break;
         }
         if (setResult) {
            System.out.println("---setting methodParam");
            result = methodParams;
         }
      }
      System.out.println("returning: " + result);
      return result;
   }

   private ITypeBinding getMethodParameterTypeForName(final String fieldName) {
      final MethodParameter methodParams = this.getMethodParams();
      if (methodParams == null) {
         return null;
      }
      for (final SingleVariableDeclaration varDecl : methodParams
            .getParameters()) {
         final IVariableBinding varBind = varDecl.resolveBinding();
         if (varBind.getName().equals(fieldName)) {
            return varBind.getType();
         }
      }
      return null;
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
                  && ((varBind.getModifiers() & Modifier.FINAL) == 0 || this.proposeFinal)) {
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
            // check for Method parameters
            if (nextType == null) {
               System.out.println("checking MethodParameters");
               nextType = this.getMethodParameterTypeForName(name);
            }

            // check for fields
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