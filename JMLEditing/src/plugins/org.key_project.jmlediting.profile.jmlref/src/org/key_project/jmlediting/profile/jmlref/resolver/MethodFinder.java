package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.profile.jmlref.resolver.typecomputer.JMLTypeComputer;

/**
 * This class is used by the {@link Resolver} to search for and to find methods of a given
 * name and a given signature/list of parameters by calling {@link #findMethod(String, List)}.
 * 
 * @author Christopher Beckmann
 *
 */
public class MethodFinder {

   private final ASTNode context;
   private final ResolverTask currentTask;
   private final ICompilationUnit compilationUnit;
   private final IASTNode originalNode;
   private final String resolveString;
   private final List<IASTNode> parameters;

   /**
    * Constructor of the method finder. It needs the following information given as
    * parameters:
    * 
    * @param context the context it starts to search as a {@link ASTNode}.
    * @param currentTask the current {@link ResolverTask} to be able to access information
    *           when needed.
    * @param compilationUnit the {@link ICompilationUnit} in case the type computer needs to
    *           be called.
    * @param originalNode the original {@link IASTNode} which should be resolved.
    */
   MethodFinder(final ASTNode context, final ResolverTask currentTask,
            final ICompilationUnit compilationUnit, final IASTNode originalNode) {
      this.context = context;
      this.currentTask = currentTask;
      this.compilationUnit = compilationUnit;
      this.originalNode = originalNode;
      resolveString = currentTask.getResolveString();
      parameters = currentTask.getParameters();
   }

   /**
    * Searches for a method with the provided name {@code resolveString} and the provided list
    * of {@code parameters} roughly following the logic in <a
    * href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.12.2"
    * >Determine Method Signature</a>.
    * 
    * @return the method declaration as an {@link ASTNode} if found or null.
    * @throws ResolverException thrown if the {@link JMLTypeComputer} throws an exception when
    *            being called or the method invocation is ambiguous.
    */
   public final ASTNode findMethod() throws ResolverException {
      
      if(context == null) {
         return null;
      }
      
      // implemented following this logic roughly:
      // 

      // compute the TypeBindings of the parameters from the IASTNodes
      final ITypeBinding[] iASTTypeBindings = getTypeBindings(parameters);

      final List<IMethodBinding> candidateList = new LinkedList<IMethodBinding>();

      // now search all the declared methods in the given context for our
      // method.
      for (final IMethodBinding methodBinding : ((TypeDeclaration) context).resolveBinding()
               .getDeclaredMethods()) {

         final ITypeBinding[] methodTypeBindings = methodBinding.getParameterTypes();

         // argument count and name equal?
         if (methodBinding.getName().equals(resolveString)
                  && methodTypeBindings.length == iASTTypeBindings.length) {
            // no arguments?
            if (methodTypeBindings.length == 0) {
               // OK, add it to our possible candidates
               candidateList.add(methodBinding);
            }
            else {
               for (int i = 0; i < methodTypeBindings.length; i++) {

                  // check for parameterized types
                  if (currentTask.getTypeArguments().size() > 0) {
                     final ITypeBinding value = currentTask.getTypeArguments().get(
                              methodTypeBindings[i].getKey());
                     if (value != null) {
                        methodTypeBindings[i] = value;
                     }
                  }

                  // call method invocation conversion on every parameter
                  if (!isMethodInvocationConversionCompatible(methodTypeBindings[i],
                           iASTTypeBindings[i])) {
                     break;
                  }
                  // if we got here and didn't break out of the loop yet
                  // and it was the last parameter => add it to the list
                  // of possible candidates
                  if (i == methodTypeBindings.length - 1) {
                     candidateList.add(methodBinding);
                  }
               }
            }
         }
      }

      IMethod method = null;

      // did we find something?
      if (candidateList.size() > 0) {
         // if there is only one... Nothing to decide on.
         if (candidateList.size() == 1) {
            method = (IMethod) candidateList.get(0).getJavaElement();
         }
         else {
            // Choose most specific method
            // Implemented following this logic:
            // http://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.12.2.5
            final ArrayList<IMethodBinding> maxSpecific = new ArrayList<IMethodBinding>();
            maxSpecific.addAll(candidateList);

            for (final IMethodBinding m1 : candidateList) {
               for (final IMethodBinding m2 : candidateList) {
                  if (m1.equals(m2)) {
                     continue;
                  }

                  // are both m1 and m2 considered max specific?
                  // is m1 strictly more specific than m2?
                  if (maxSpecific.contains(m1) && maxSpecific.contains(m2)
                           && isMoreSpecific(m1, m2) && !isMoreSpecific(m2, m1)) {
                     maxSpecific.remove(m2);
                  }
               }
            }

            // do we have methods left?
            if (maxSpecific.size() > 0) {
               // do we have more than 1? :(
               if (maxSpecific.size() > 1) {
                  throw new ResolverException("The method invocation is ambiguous.",
                           originalNode, null);
               }
               method = (IMethod) maxSpecific.get(0).getJavaElement();
            }
            else {
               return null;
            }
         }
      }
      // get the JDTNode for it.
      return findIMethod(context, method);
   }

   /**
    * This is a helper method to help with method resolving. It checks whether the given types
    * correlate to each other by Method Invocation Conversion rules. <br>
    * See: <a href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.3">
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.3</a> as a reference.
    * 
    * @param that the type the method definition has
    * @param other the type the method is called with
    * @return true, if the types correlate after Method Invocation Conversion rules. False
    *         otherwise.
    */
   private boolean isMethodInvocationConversionCompatible(final ITypeBinding that,
            final ITypeBinding other) {

      return that.isEqualTo(other) || isWideningPrimitiveConversionCompatible(that, other)
               || isWideningReferenceConversionCompatible(that, other);
   }

   /**
    * Helper Method. Checks if the {@code other} type is a sub type of the {@code that} type.
    * See: <a href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.5">
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.5</a>
    * 
    * @param that the type the method definition has
    * @param other the type the method is called with
    * @return true, if {@code other} is a sub type of {@code that}. False otherwise.
    */
   private boolean isWideningReferenceConversionCompatible(final ITypeBinding that,
            final ITypeBinding other) {
      ITypeBinding cother = other;

      if (that == null || that.isPrimitive()) {
         return false;
      }
      if (other == null) {
         return false;
      }
      // if the calling type is the null type we return true, because null can be any type.
      if (other.isNullType()) {
         return true;
      }
      if (other.isPrimitive()) {
         cother = boxPrimitiveType(other);
      }
      if (cother == null) {
         return false;
      }

      // get lists, so we don't check interfaces multiple times
      final ArrayList<ITypeBinding> checked = new ArrayList<>();
      final ArrayList<ITypeBinding> leftToCheck = new ArrayList<>();

      // Check Super classes and gather interfaces on the way
      for (ITypeBinding current = cother; current != null; current = current.getSuperclass()) {

         if (current.isEqualTo(that)) {
            return true;
         }

         for (final ITypeBinding i : current.getInterfaces()) {
            if (!leftToCheck.contains(i)) {
               leftToCheck.add(i);
            }
         }
      }

      // check gathered interfaces
      while (leftToCheck.size() > 0) {
         final ITypeBinding i = leftToCheck.get(0);

         if (i.isEqualTo(that)) {
            return true;
         }

         checked.add(i);
         leftToCheck.remove(i);

         for (final ITypeBinding j : i.getInterfaces()) {
            if (!leftToCheck.contains(j) && !checked.contains(j)) {
               leftToCheck.add(j);
            }
         }
      }

      return false;
   }

   /**
    * Helper Method. Checks if the {@code other} type can be extended to the {@code that}
    * type. See: <a
    * href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.2">
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.2</a>
    * 
    * @param that the type the method definition has
    * @param other the type the method is called with
    * @return true, if {@code other} can be extended to {@code that}. False otherwise.
    */
   private boolean isWideningPrimitiveConversionCompatible(final ITypeBinding that,
            final ITypeBinding other) {
      ITypeBinding cother = other;
      ITypeBinding cthat = that;

      if (that == null) {
         return false;
      }
      if (other == null) {
         return false;
      }

      if (!other.isPrimitive()) {
         cother = unboxPrimitiveType(other);
      }
      if (!that.isPrimitive()) {
         cthat = unboxPrimitiveType(that);
      }

      if (cother == null || cthat == null) {
         return false;
      }
      // comparing strings is actually easier than creating the types and
      // comparing them.
      final String thatName = cthat.getQualifiedName();
      final String otherName = cother.getQualifiedName();
      final String bYTE = "byte";
      final String sHORT = "short";
      final String iNT = "int";
      final String lONG = "long";
      final String fLOAT = "float";
      final String dOUBLE = "double";
      final String cHAR = "char";

      if (thatName.equals(otherName)) {
         return true;
      }

      if (otherName.equals(bYTE)
               && (thatName.equals(sHORT) || thatName.equals(iNT) || thatName.equals(lONG)
                        || thatName.equals(fLOAT) || thatName.equals(dOUBLE))) {
         return true;
      }

      if (otherName.equals(sHORT)
               && (thatName.equals(iNT) || thatName.equals(lONG) || thatName.equals(fLOAT) || thatName
                        .equals(dOUBLE))) {
         return true;
      }

      if (otherName.equals(cHAR)
               && (thatName.equals(iNT) || thatName.equals(lONG) || thatName.equals(fLOAT) || thatName
                        .equals(dOUBLE))) {
         return true;
      }

      if (otherName.equals(iNT)
               && (thatName.equals(lONG) || thatName.equals(fLOAT) || thatName.equals(dOUBLE))) {
         return true;
      }

      if (otherName.equals(lONG) && (thatName.equals(fLOAT) || thatName.equals(dOUBLE))) {
         return true;
      }

      if (otherName.equals(fLOAT) && thatName.equals(dOUBLE)) {
         return true;
      }

      return false;
   }

   /**
    * Finds the {@link MethodDeclaration} corresponding to the given {@link IMethod}.
    * 
    * @param context the context to find the {@link MethodDeclaration} in.
    * @param method the {@link IMethod} to search for.
    * @return the {@link MethodDeclaration} or {@code null} if nothing has been found.
    */
   private MethodDeclaration findIMethod(final ASTNode context, final IMethod method) {
      if (method == null || context == null) {
         return null;
      }

      final LinkedList<MethodDeclaration> result = new LinkedList<MethodDeclaration>();

      final String[] expectedParameterKeys = Signature.getParameterTypes(method.getKey());

      context.accept(new ASTVisitor() {
         @Override
         public boolean visit(final MethodDeclaration node) {
            if (node.getName().getIdentifier().equals(method.getElementName())) {
               final String[] actualParameterKeys = Signature.getParameterTypes(node
                        .resolveBinding().getKey());
               if (actualParameterKeys.length == expectedParameterKeys.length) {

                  for (int i = 0; i < actualParameterKeys.length; i++) {
                     if (!actualParameterKeys[i].equals(expectedParameterKeys[i])) {
                        return true;
                     }
                     else {
                        continue;
                     }
                  }

                  result.add(node);
                  return false;
               }
            }
            return true;
         }
      });

      if (result.isEmpty()) {
         return null;
      }

      return result.poll();
   }

   /**
    * Performs unboxing of primitive types. <br>
    * See: <a href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.8">
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.8</a>
    * 
    * @param other the {@link ITypeBinding} to be unboxed.
    * @return the {@link ITypeBinding} of the unboxed type or null if the type can not be
    *         unboxed.
    */
   private ITypeBinding unboxPrimitiveType(final ITypeBinding other) {
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Boolean"))) {
         return context.getAST().resolveWellKnownType("boolean");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Byte"))) {
         return context.getAST().resolveWellKnownType("byte");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Short"))) {
         return context.getAST().resolveWellKnownType("short");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Character"))) {
         return context.getAST().resolveWellKnownType("char");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Integer"))) {
         return context.getAST().resolveWellKnownType("int");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Long"))) {
         return context.getAST().resolveWellKnownType("long");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Float"))) {
         return context.getAST().resolveWellKnownType("float");
      }
      if (other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Double"))) {
         return context.getAST().resolveWellKnownType("double");
      }
      return null;
   }

   /**
    * Performs boxing of primitive types. <br>
    * See: <a href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.7">
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.7</a>
    * 
    * @param other the {@link ITypeBinding} to be boxed.
    * @return the {@link ITypeBinding} of the boxed type or null if the type can not be boxed.
    */
   private ITypeBinding boxPrimitiveType(final ITypeBinding other) {
      if (other.getQualifiedName().equals("boolean")) {
         return context.getAST().resolveWellKnownType("java.lang.Boolean");
      }
      if (other.getQualifiedName().equals("byte")) {
         return context.getAST().resolveWellKnownType("java.lang.Byte");
      }
      if (other.getQualifiedName().equals("short")) {
         return context.getAST().resolveWellKnownType("java.lang.Short");
      }
      if (other.getQualifiedName().equals("char")) {
         return context.getAST().resolveWellKnownType("java.lang.Character");
      }
      if (other.getQualifiedName().equals("int")) {
         return context.getAST().resolveWellKnownType("java.lang.Integer");
      }
      if (other.getQualifiedName().equals("long")) {
         return context.getAST().resolveWellKnownType("java.lang.Long");
      }
      if (other.getQualifiedName().equals("float")) {
         return context.getAST().resolveWellKnownType("java.lang.Float");
      }
      if (other.getQualifiedName().equals("double")) {
         return context.getAST().resolveWellKnownType("java.lang.Double");
      }
      return null;
   }

   /**
    * When more than one method is both applicable and accessible to a method invocation. We
    * then have to choose the most specific one. This method tells you whether a method
    * {@code m1} is more specific than a method {@code m2}. <br>
    * See <a
    * href="https://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.12.2.5">
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.12.2.5</a>
    * 
    * @param m1 the first method
    * @param m2 the second method
    * @return {@code true}, if the first method is more specific than the second,
    *         {@code false} otherwise.
    */
   private boolean isMoreSpecific(final IMethodBinding m1, final IMethodBinding m2) {
      final ITypeBinding[] types1 = m1.getParameterTypes();
      final ITypeBinding[] types2 = m2.getParameterTypes();
      if (types1.length != types2.length || types1.length == 0) {
         return false;
      }
      for (int i = 0; i < types1.length; i++) {
         if (!types1[i].isEqualTo(types2[i]) && !types1[i].isSubTypeCompatible(types2[i])) {
            return false;
         }
      }
      return true;
   }

   /**
    * Gets the {@link ITypeBinding}s of the given {@link IASTNode}s from the
    * {@link JMLTypeComputer}.
    * 
    * @param parameters the {@link IASTNode}s to check
    * @return an array of {@link ITypeBinding}s corresponding to the given parameter list
    * @throws ResolverException if the {@link JMLTypeComputer} throws a
    *            {@link TypeComputerException}.
    */
   private ITypeBinding[] getTypeBindings(final List<IASTNode> parameters)
            throws ResolverException {
      // if the parameter list is empty, return an empty array
      if (parameters.size() == 0) {
         return new ITypeBinding[0];
      }

      // create an array that can hold the results
      final ITypeBinding[] result = new ITypeBinding[parameters.size()];

      // get a typeComputer
      final JMLTypeComputer tc = new JMLTypeComputer(compilationUnit);

      // save the computed types into the array
      for (int i = 0; i < parameters.size(); i++) {
         try {
            result[i] = tc.computeType(parameters.get(i));
         }
         catch (final TypeComputerException e) {
            throw new ResolverException(
                     "TypeComputer threw an exception when trying to compute the type of a method parameter.",
                     originalNode, e);
         }
      }
      return result;
   }
}
