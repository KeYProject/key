package org.key_project.jmlediting.core.resolver.typecomputer;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.util.JavaBasicsNodeTypes;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.util.jdt.JDTUtil;


public class TypeComputer implements ITypeComputer {

   protected ICompilationUnit compilationUnit;
   protected IResolver resolver;

   final protected ITypeBinding P_FLOAT, P_INTEGER, P_CHAR, FLOAT, INTEGER, CHAR;

   public TypeComputer(final ICompilationUnit compilationUnit, final IResolver resolver) {
      this.compilationUnit = compilationUnit;
      this.resolver = resolver;

      P_FLOAT = createWellKnownType("float");
      P_INTEGER = createWellKnownType("int");
      P_CHAR = createWellKnownType("char");
      FLOAT = createWellKnownType("java.lang.Float");
      INTEGER = createWellKnownType("java.lang.Integer");
      CHAR = createWellKnownType("java.lang.Character");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ITypeBinding computeType(final IASTNode node) throws TypeComputerException {

      if (node == null) {
         return null;
      }

      if (node.getType() == NodeTypes.STRING) {
         // TODO: possible we have to do something here...
         return null;

      }
      else if (node.getType() == NodeTypes.KEYWORD) {
         return null;

      }
      else if (node.getType() == NodeTypes.KEYWORD_APPL) {
         return null;

      }
      else if (node.getType() == NodeTypes.KEYWORD_CONTENT) {
         return null;

      }
      else if (node.getType() == NodeTypes.NODE) {
         return null;

      }
      else if (node.getType() == NodeTypes.LIST) {
         return null;

      }
      else if (node.getType() == NodeTypes.SEQ) {
         return null;

      }
      else if (node.getType() == NodeTypes.SOME) {
         return null;

      }
      else if (node.getType() == NodeTypes.NONE) {
         return null;

      }
      throw new TypeComputerException("Can not identify the node type.", node);
   }

   /**
    * Returns the return Type of the given IBinding. <br>
    * If it is an {@link IMethodBinding} then the return type of the method is returned. <br>
    * If it is an {@link IVariableBinding} the type of the variable is returned. <br>
    * If it is an {@link ITypeBinding} it will return the type itself.
    * 
    * @param binding the {@link IBinding} to get the {@link ITypeBinding} from.
    * @return the corresponding {@link ITypeBinding}
    */
   public static ITypeBinding getTypeFromBinding(final IBinding binding) {
      if (binding instanceof IVariableBinding) {
         return ((IVariableBinding) binding).getType();
      }
      else if (binding instanceof IMethodBinding) {
         return ((IMethodBinding) binding).getReturnType();
      }
      else if (binding instanceof ITypeBinding) {
         return (ITypeBinding) binding;
      }
      return null;
   }

   /**
    * Tests if the given {@link IASTNode} is one of the types specified in
    * {@link JavaBasicsNodeTypes}.
    * 
    * @param node the {@link IASTNode} to test
    * @return true, if the type of the {@link IASTNode} is specified in the
    *         {@link JavaBasicsNodeTypes} class.
    */
   protected final boolean isPrimitive(final IASTNode node) {
      final int type = node.getType();
      return type == JavaBasicsNodeTypes.BOOLEAN_LITERAL
               || type == JavaBasicsNodeTypes.CHARACTER_LITERAL
               || type == JavaBasicsNodeTypes.FLOAT_LITERAL
               || type == JavaBasicsNodeTypes.INTEGER_LITERAL
               || type == JavaBasicsNodeTypes.NULL_LITERAL
               || type == JavaBasicsNodeTypes.STRING_LITERAL
               || type == JavaBasicsNodeTypes.NAME;
   }

   /**
    * If the given {@link IASTNode} represents a primitive type, then this function will
    * return the {@link ITypeBinding} for it.
    * 
    * @param node the {@link IASTNode} to check
    * @return the corresponding {@link ITypeBinding} or null
    */
   protected final ITypeBinding getType(final IASTNode node) {

      final int type = node.getType();
      if (type == JavaBasicsNodeTypes.BOOLEAN_LITERAL) {
         return createWellKnownType("boolean");
      }
      else if (type == JavaBasicsNodeTypes.CHARACTER_LITERAL) {
         return createWellKnownType("char");
      }
      else if (type == JavaBasicsNodeTypes.FLOAT_LITERAL) {
         return createWellKnownType("float");
      }
      else if (type == JavaBasicsNodeTypes.INTEGER_LITERAL) {
         return createWellKnownType("int");
      }
      else if (type == JavaBasicsNodeTypes.NULL_LITERAL) {
         // TODO .. type of null?
         // return createWellKnownType("");
      }
      else if (type == JavaBasicsNodeTypes.STRING_LITERAL) {
         return createWellKnownType("java.lang.String");
      }
      else if (type == JavaBasicsNodeTypes.NAME) {
         // TODO .. what is name?
         //System.out.println("No IType of NodeType");
         return null; // createWellKnownType("NAME"); // should never happen
      }
      return null;
   }

   protected final ITypeBinding createWellKnownType(final String type) {
      return JDTUtil.parse(compilationUnit).getAST().resolveWellKnownType(type);
   }

   /**
    * Calls the {@link IResolver} that was provided when creating the TypeComputer and
    * resolves the given {@link IASTNode} with it.
    * 
    * @param node the {@link IASTNode} that will be resolved
    * @return the resulting {@link ITypeBinding}
    * @throws TypeComputerException if the {@link IResolver} can not resolve the
    *            {@link IASTNode}
    */
   protected final ITypeBinding callResolver(final IASTNode node)
            throws TypeComputerException {
      return callResolver(node, resolver);
   }

   /**
    * Calls the specified {@link IResolver} and resolves the given {@link IASTNode} with it.
    * 
    * @param node the {@link IASTNode} that will be resolved
    * @param resolver the {@link IResolver} to be used when resolving.
    * @return the resulting {@link ITypeBinding}
    * @throws TypeComputerException if the {@link IResolver} can not resolve the
    *            {@link IASTNode}
    */
   protected final ITypeBinding callResolver(final IASTNode node, final IResolver resolver)
            throws TypeComputerException {
      ResolveResult result = null;

      try {
         result = resolver.resolve(compilationUnit, node);
         while (resolver.hasNext()) {
            result = resolver.next();
         }
      }
      catch (final ResolverException e) {
         LogUtil.getLogger().logError(e);
         throw new TypeComputerException("Got ResolverException, when trying to resolve "
                  + node.prettyPrintAST(), node, e);
      }
      if (result != null) {
         return getTypeFromBinding(result.getBinding());
      }
      throw new TypeComputerException("Given Resolver could not resolve the node.", node);
   }

   /*
    * "boolean" •"byte" •"char" •"double" •"float" •"int" •"long" •"short" •"void"
    * •"java.lang.AssertionError" (since 3.7) •"java.lang.Boolean" (since 3.1)
    * •"java.lang.Byte" (since 3.1) •"java.lang.Character" (since 3.1) •"java.lang.Class"
    * •"java.lang.Cloneable" •"java.lang.Double" (since 3.1) •"java.lang.Error"
    * •"java.lang.Exception" •"java.lang.Float" (since 3.1) •"java.lang.Integer" (since 3.1)
    * •"java.lang.Long" (since 3.1) •"java.lang.Object" •"java.lang.RuntimeException"
    * •"java.lang.Short" (since 3.1) •"java.lang.String" •"java.lang.StringBuffer"
    * •"java.lang.Throwable" •"java.lang.Void" (since 3.1) •"java.io.Serializable"
    */
}
