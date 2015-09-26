package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.IPackageBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.TypeParameter;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.core.search.SearchPattern;
import org.eclipse.jdt.core.search.TypeNameMatch;
import org.eclipse.jdt.core.search.TypeNameMatchRequestor;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.typecomputer.JMLTypeComputer;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

/**
 * The Resolver class, that only has three public methods. <br>
 * "{@code resolve}({@link ICompilationUnit}, {@link IASTNode}) ->
 * {@link ResolveResult}" that will resolve the {@link IASTNode} given and find
 * the corresponding JavaElement or JML declaration and <br>
 * "{@code next()} -> {@link ResolveResult}" that will resolve any member access
 * that is appended to the original identifier. <br>
 * "{@code hasNext()} -> boolean" that will return true, if the taskList is not
 * empty and there is still something to resolve with the next() method.
 * 
 * @author Christopher Beckmann
 */
public class Resolver implements IResolver {

   /**
    * ResolverTask is a container for information, that will be used every time
    * next() is called in the {@link Resolver} class.
    * 
    * @author Christopher Beckmann
    */
   private final class ResolverTask {
      private boolean isMethod = false;
      private boolean isArrayAcess = false;
      private boolean isKeyword = false;
      private boolean isClass = false;
      private boolean isArray = false;
      private boolean isTypeVariable = false;
      private int skipIdentifier = 0;
      private String resolveString = null;
      private IStringNode node = null;
      private ResolveResult lastResult = null;
      private ITypeBinding originalTypeBinding;
      private final Map<String, ITypeBinding> typeArguments = new HashMap<String, ITypeBinding>();
      private final List<IASTNode> parameters = new LinkedList<IASTNode>();
   }

   private ASTNode context = null;
   private ICompilationUnit compilationUnit = null;
   private final Map<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();
   private final List<ImportDeclaration> imports = new ArrayList<ImportDeclaration>();
   private final List<ImportDeclaration> onDemandImports = new ArrayList<ImportDeclaration>();
   private final LinkedList<ResolverTask> tasks = new LinkedList<ResolverTask>();
   private ResolverTask currentTask = null;
   private PackageDeclaration pack = null;
   private IASTNode originalNode = null;
   private int skipIdentifier = 0;

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("unchecked")
   @Override
   public final ResolveResult resolve(final ICompilationUnit compilationUnit, final IASTNode jmlNode) throws ResolverException {

      // check if the given IASTNode is correct and get possible information
      if(jmlNode == null || compilationUnit == null) {
         return null;
      }

      // reset everything .. so we can resolve more than once, with one instance of a resolver
      reset(compilationUnit);
      
      originalNode = jmlNode;
      
      // First, we get all the information about, what we have to resolve by checking the given IASTNode.
      // this builds up the task list.
      buildResolverTask(jmlNode);

      // Parse JML and map nodes to JDT
      // Parse JDT first
      final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(compilationUnit);

      final List<ImportDeclaration> importList = jdtAST.imports();
      for(final ImportDeclaration i : importList) {
         if(i.isOnDemand()) {
            onDemandImports.add(i);
         } else {
            imports.add(i);
         }
      }

      pack = jdtAST.getPackage();

      // Locate the comments
      String source = null;
      try {
         source = compilationUnit.getSource();
      } catch(final JavaModelException e) {
         // CompilationUnit has no source attached to it?
         LogUtil.getLogger().logError(e);
         return null;
      }

      // Finding the whole JML comment which contains our IASTNode by
      // getting all JDT comments (everything with // or /*)
      // and filtering those for comments which start with either //@ or /*@
      final List<Comment> jdtComments = jdtAST.getCommentList();

      final ArrayList<Comment> jmlComments = new ArrayList<Comment>();

      Comment jmlComment = null;

      // Filtering the JDT comments
      for(final Comment comment : jdtComments) {

         final int commentStart = comment.getStartPosition();
         final String stringToCompare = source.substring(commentStart, commentStart + 3);

         if(stringToCompare.equals("//@") || stringToCompare.equals("/*@")) {
            jmlComments.add(comment);

            // check if the JML comment contains our IASTNode that is
            // supposed to be resolved
            if(commentStart <= jmlNode.getStartOffset() && commentStart + comment.getLength() >= jmlNode.getEndOffset()) {
               jmlComment = comment;
            }
         }
      }

      // this maps every jdt comment to the jdt ASTNode it belongs to.
      jdtAST.accept(new ASTVisitor() {

         @Override
         public boolean preVisit2(final ASTNode node) {
            // Check if the node has a comment at all
            final int start = jdtAST.firstLeadingCommentIndex(node);
            if(start != -1) {
               // extended start = start if JML in between Javadoc and Node (e.g. method)
               // extended start < start if JML above Javadoc.
               // Note that it will not be extended if an empty line is between JML and Javadoc.
               final int extStartNode = jdtAST.getExtendedStartPosition(node);
               final int extEndNode = extStartNode + jdtAST.getExtendedLength(node);
               // JML belongs to the node if it is in between the extended
               // area covered by the node
               for(final Comment comment : jmlComments) {
                  final int commentStart = comment.getStartPosition();
                  final int commentEnd = commentStart + comment.getLength();
                  if(commentStart >= extStartNode && commentEnd < extEndNode) {
                     if(node.getNodeType() == ASTNode.PRIMITIVE_TYPE || node.getNodeType() == ASTNode.SIMPLE_TYPE) {
                        commentToAST.put(comment, node.getParent());
                     } else {
                        commentToAST.put(comment, node);
                     }
                  }
               }
            }
            return super.preVisit2(node);
         }
      });

      // Check if there are any JML comments not yet mapped.
      // Those should be class invariants not directly written above a field or such.
      // Put the TypeDecleration of the CompilationUnit/ASTNode into commentToAST.
      // Method invariants should have been mapped before.
      for(final Comment comment : jmlComments) {
         if(!commentToAST.containsKey(comment)) {
            final ASTNode compUnitType = getTypeInCompilationUnit(
                  compilationUnit.getElementName().substring(0, compilationUnit.getElementName().lastIndexOf('.')), jdtAST);
            commentToAST.put(comment, compUnitType);
         }
      }

      // now we have all the information we need
      context = commentToAST.get(jmlComment);

      return next();
   }

   /**
    * Reset everything to their default values.
    * 
    * @param compilationUnit
    *           the {@link ICompilationUnit} to reset to.
    */
   private void reset(final ICompilationUnit compilationUnit) {
      context = null;
      this.compilationUnit = compilationUnit;
      originalNode = null;
      commentToAST.clear();
      imports.clear();
      onDemandImports.clear();
      tasks.clear();
      currentTask = null;
      pack = null;
      skipIdentifier = 0;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final ResolveResult next() throws ResolverException {
      currentTask = tasks.poll();
      // no more task?
      if(currentTask == null) {
         return null;
      }

      ASTNode jdtNode = null;
      IBinding binding = null;
      ITypeBinding returnValue = null;
      ResolveResultType resolveResultType = null;

      if(!currentTask.isArrayAcess) {

         if(currentTask.isKeyword) {
            jdtNode = processKeyword();
         } else {
            jdtNode = findIdentifier();
         }

         
         // if we have multiple of the same task in here
         // because we are trying to find something from a TypeParameter 
         // we keep on going with the next task instead of returning null
         if(skipIdentifier != 0 && !currentTask.isTypeVariable) {
            if(tasks.peek() != null && skipIdentifier == tasks.peek().skipIdentifier) {
               if(jdtNode == null) {
                  return next();
               } else {
                  // If we found something we remove the rest of the tasks with our skip identifier
                  // so we can work normally after that
                  final List<ResolverTask> toRemove = new LinkedList<ResolverTask>();
                  for(final ResolverTask t : tasks) {
                     if(t.skipIdentifier == skipIdentifier) {
                        toRemove.add(t);
                     }
                  }
                  // I have to do this like this, because removing an element from the list above,
                  // will terminate it earlier than I actually want it to.
                  for(final ResolverTask t : toRemove) {
                     tasks.remove(t);
                  }
               }
            }
            // reset skip identifier to either the next task or if its not part 0
            if(tasks.peek() != null) {
               skipIdentifier = tasks.peek().skipIdentifier;
            }
         }
         
         // Are we trying to access functions of a TypeParameter?
         if(jdtNode == null && currentTask.isTypeVariable || jdtNode instanceof TypeParameter) {
            
            // We don't know the final types yet. So we get all the type bounds.
            final ITypeBinding[] bounds = jdtNode == null ? currentTask.lastResult.getReturnType().getTypeBounds() : ((TypeParameter)jdtNode).resolveBinding().getTypeBounds();
            // Do we have bounds? If not .. we can not access anything on this type. Because we don't know what type it will be.
            if(bounds.length > 0) {
               // remove the next task and replace it with our versions
               final ResolverTask nextTask = jdtNode == null ? currentTask : tasks.poll();
               ResolveResult result = null;
               final int identifier = nextTask.hashCode();
               skipIdentifier = identifier;
               for(final ITypeBinding t : bounds) {
                  tasks.addFirst(new ResolverTask());
                  tasks.getFirst().isArrayAcess = nextTask.isArrayAcess;
                  tasks.getFirst().isClass = nextTask.isClass;
                  tasks.getFirst().isKeyword = nextTask.isKeyword;
                  tasks.getFirst().isMethod = nextTask.isMethod;
                  tasks.getFirst().node = nextTask.node;
                  tasks.getFirst().parameters.addAll(nextTask.parameters);
                  tasks.getFirst().resolveString = nextTask.resolveString;
                  tasks.getFirst().skipIdentifier = identifier;
                  result = new ResolveResult(jdtNode, resolveResultType, binding, t, currentTask.node);
                  tasks.getFirst().lastResult = result;
               }
            } else {
               // If there is no bound.. set the next context to Object. Those functions are everywhere.
               returnValue = context.getAST().resolveWellKnownType("java.lang.Object");
               currentTask.isTypeVariable = false;
               currentTask.lastResult = new ResolveResult(currentTask.lastResult.getJDTNode(), currentTask.lastResult.getResolveType(), currentTask.lastResult.getBinding(), returnValue, currentTask.lastResult.getStringNode());
               tasks.add(currentTask);
            }
            if(jdtNode == null) {
               return next();
            }
         }
         
         if(!currentTask.isArray) {
            if(jdtNode == null) {
               // set context to null so we don't give out wrong information on
               // a following next() call.              
               context = null;
               return null;
            }
   
            // get more information to pass on.            
            binding = resolveBinding(jdtNode);
            returnValue = TypeComputer.getTypeFromBinding(binding);
            resolveResultType = getResolveType(jdtNode);
         }
      } else {
         // Array Access
         jdtNode = currentTask.lastResult.getJDTNode();
         binding = TypeComputer.getTypeFromBinding(currentTask.lastResult.getBinding()).getComponentType();
         returnValue = TypeComputer.getTypeFromBinding(binding);
         resolveResultType = ResolveResultType.ARRAY_ACCESS;
         
         
         if(binding == null) {
            throw new ResolverException("Tried to perform an array access on a non array.", originalNode, null);
         }
      }
           
      // If we have parameterized types in our result. 
      // We have to add the real result as an additional parameter.
      if(currentTask.typeArguments.size() > 0) {
         final ITypeBinding value = currentTask.typeArguments.get(returnValue.getKey());
         if(value != null) {
            returnValue = value;
         }
      }

      if(currentTask.isArray) {
         if(currentTask.resolveString.equals("length")) {
            returnValue = context.getAST().resolveWellKnownType("int");
            final ResolveResult finalResult = new ResolveResult(null, ResolveResultType.ARRAY_LENGTH, returnValue, returnValue, currentTask.node);
            return finalResult;
         } else if(currentTask.resolveString.equals("clone")) {
            returnValue = currentTask.originalTypeBinding;
            binding = resolveBinding(jdtNode);
         } else {
            // this is a method we can pass on
            binding = resolveBinding(jdtNode);
            returnValue = TypeComputer.getTypeFromBinding(binding);
            resolveResultType = getResolveType(jdtNode);
         }
      }
      
      final ResolveResult finalResult = new ResolveResult(jdtNode, resolveResultType, binding, returnValue, currentTask.node);

      if(tasks.peek() != null) {
         tasks.peek().lastResult = finalResult;
      }
      return finalResult;
   }

   private ASTNode processKeyword() throws ResolverException {
      if(currentTask.isKeyword) {
         if(currentTask.resolveString.equals("this")) {
            return getDeclaringClass(context);
         } else if(currentTask.resolveString.equals("super")) {
            return getDeclaringClass(context).getSuperclassType();
         } else if(currentTask.resolveString.equals("\\result")) {
            return findMethodReturnValue(context);
         }
      }
      return null;
   }

   private TypeDeclaration getDeclaringClass(final ASTNode context) {
      ASTNode clazz = context;
      while(clazz != null && !(clazz instanceof TypeDeclaration) && clazz.getParent() != null) {
         clazz = clazz.getParent();
      }
      return (TypeDeclaration) clazz;
   }

   private ASTNode findMethodReturnValue(final ASTNode context) {
      if(context instanceof MethodDeclaration) {
         return ((MethodDeclaration) context).getReturnType2();
      } else {
         return null;
      }
   }

   /**
    * Searches for the {@link ASTNode} specified by {@code currentTask}.
    * 
    * @return the {@link ASTNode} or null if it could not be found
    * @throws ResolverException
    *            is thrown if the setNewContext, findMethod or findInImports methods throws a
    *            ResolverException
    */
   private ASTNode findIdentifier() throws ResolverException {
      // Initialize jdtNode with null. If this ever changes to something else,
      // we found our node!
      ASTNode jdtNode = null;

      // Set the context.
      // Very important method call!
      context = setNewContext();

      // is this a type variable? 
      // then get to the end part so we can start building ResolveResults
      if(currentTask.isTypeVariable) {
         return null;
      }
         
      // start with searching for parameters if we are not searching for a
      // method or a class
      // if lastResult is null, this must be the first call of next() and is
      // the only case we could find parameters in
      if(currentTask.lastResult == null && !currentTask.isMethod && !currentTask.isClass && !currentTask.isArray) {
         jdtNode = findParameters(context, currentTask.resolveString);
      }

      // we need to get more information, in particular which class declared the method/field.
      // if our context is already set to a TypeDeclaration nothing will change.
      context = getDeclaringClass(context);

      // are we searching for a method?
      if(jdtNode == null && currentTask.isMethod) {

         // TODO: Variable Arity Methods are not supported yet.
         // TODO: Wildcards not supported yet.

         ASTNode searchContext = context;

         do {
            jdtNode = findMethod(searchContext, currentTask.resolveString, currentTask.parameters);
            searchContext = getSuperClass(searchContext);
            
         } while(jdtNode == null && searchContext != null);
      }
      if(jdtNode == null && !currentTask.isClass && !currentTask.isArray) {
         
         ASTNode searchContext = context;

         do {
            jdtNode = findField(searchContext, currentTask.resolveString);
            searchContext = getSuperClass(searchContext);
            
         } while(jdtNode == null && searchContext != null);
      }
      if(jdtNode == null && !currentTask.isArray) {
         jdtNode = findTypeParameter(currentTask.resolveString);
      }
      if(jdtNode == null && !currentTask.isArray) {
         jdtNode = findInImports(currentTask.resolveString, imports);
      }
      if(jdtNode == null && !currentTask.isArray) {
         jdtNode = findInPackage(currentTask.resolveString, pack.resolveBinding());
      }
      if(jdtNode == null && !currentTask.isArray) {
         jdtNode = findInImports(currentTask.resolveString, onDemandImports);
      }
      if(jdtNode == null && !currentTask.isArray) {
         jdtNode = findInPackage(currentTask.resolveString, "java.lang");
      }
      if(jdtNode == null && !currentTask.isArray) {
         jdtNode = findNextReferencesClass(currentTask.resolveString);
      }

      // return what we found... either null or the jdtNode
      return jdtNode;
   }

   private ASTNode findTypeParameter(final String resolveString) {
      final List<TypeParameter> result = new LinkedList<TypeParameter>();
      context.accept(new ASTVisitor() {
         
         @Override
         public boolean visit(final TypeParameter node) {
            if(node.getName().getIdentifier().equals(resolveString)) {
               result.add(node);
               return false;
            }
            return true;
         }
      });
      return result.size() > 0 ? result.get(0) : null;
   }

   private TypeDeclaration getSuperClass(final ASTNode searchContext) {
      if(searchContext == null) {
         return null;
      }
      // Set new context to super class and call it again until we
      // reach Object
      final Type superClass = getDeclaringClass(searchContext).getSuperclassType();
      IType type = null;

      if(superClass == null) {
         // Create a TypeBinding of object to compare
         final ITypeBinding objectTypeBinding = context.getAST().resolveWellKnownType("java.lang.Object");

         if(((TypeDeclaration) searchContext).resolveBinding().isEqualTo(objectTypeBinding)) {
            return null;
         }
         try {
            type = compilationUnit.getJavaProject().findType(objectTypeBinding.getQualifiedName());
         } catch(final JavaModelException e) {
            LogUtil.getLogger().logError(e);
         }
      } else {
         type = (IType) superClass.resolveBinding().getJavaElement();
      }
      if(type == null) {
         return null;
      }

      ASTNode node = null;
      if(type.getClassFile() != null) {
         node = JDTUtil.parse(type.getClassFile());
      } else if(type.getCompilationUnit() != null) {
         node = JDTUtil.parse(type.getCompilationUnit());
      }
      return getTypeInCompilationUnit(type.getElementName(), node);
   }
   
   private ASTNode findMethod(final ASTNode context, final String resolveString, final List<IASTNode> parameters) throws ResolverException {

      // implemented following this logic roughly:
      // https://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.12.2

      // compute the TypeBindings of the parameters from the IASTNodes
      final ITypeBinding[] iASTTypeBindings = getTypeBindings(parameters);

      final List<IMethodBinding> candidateList = new LinkedList<IMethodBinding>();

      // now search all the declared methods in the given context for our
      // method.
      for(final IMethodBinding methodBinding : ((TypeDeclaration) context).resolveBinding().getDeclaredMethods()) {

         final ITypeBinding[] methodTypeBindings = methodBinding.getParameterTypes();

         // argument count and name equal?
         if(methodBinding.getName().equals(resolveString) && methodTypeBindings.length == iASTTypeBindings.length) {
            // no arguments?
            if(methodTypeBindings.length == 0) {
               // OK, add it to our possible candidates
               candidateList.add(methodBinding);
            } else {
               for(int i = 0; i < methodTypeBindings.length; i++) {
                  
                  // check for parameterized types
                  if(currentTask.typeArguments.size() > 0) {
                     final ITypeBinding value = currentTask.typeArguments.get(methodTypeBindings[i].getKey());
                     if(value != null) {
                        methodTypeBindings[i] = value;
                     }
                  }
                  
                  // call method invocation conversion on every parameter
                  if(!isMethodInvocationConversionCompatible(methodTypeBindings[i], iASTTypeBindings[i])) {
                     break;
                  }
                  // if we got here and didn't break out of the loop yet
                  // and it was the last parameter => add it to the list
                  // of possible candidates
                  if(i == methodTypeBindings.length - 1) {
                     candidateList.add(methodBinding);
                  }
               }
            }
         }
      }

      IMethod method = null;

      // did we find something?
      if(candidateList.size() > 0) {
         // if there is only one... Nothing to decide on.
         if(candidateList.size() == 1) {
            method = (IMethod) candidateList.get(0).getJavaElement();
         } else {
            // Choose most specific method
            // Implemented following this logic:
            // http://docs.oracle.com/javase/specs/jls/se7/html/jls-15.html#jls-15.12.2.5
            final ArrayList<IMethodBinding> maxSpecific = new ArrayList<IMethodBinding>();
            maxSpecific.addAll(candidateList);

            for(final IMethodBinding m1 : candidateList) {
               for(final IMethodBinding m2 : candidateList) {
                  if(m1.equals(m2)) {
                     continue;
                  }

                  // are both m1 and m2 considered max specific?
                  // is m1 strictly more specific than m2?
                  if(maxSpecific.contains(m1) && maxSpecific.contains(m2) && isMoreSpecific(m1, m2) && !isMoreSpecific(m2, m1)) {
                     maxSpecific.remove(m2);
                  }
               }
            }

            // do we have methods left?
            if(maxSpecific.size() > 0) {
               // do we have more than 1? :(
               if(maxSpecific.size() > 1) {
                  throw new ResolverException("The method invocation is ambiguous.", originalNode, null);
               }
               method = (IMethod) maxSpecific.get(0).getJavaElement();
            } else {
               return null;
            }
         }
      }
      // get the JDTNode for it.
      return findIMethod(context, method);
   }

   /**
    * This is a helper method to help with method resolving. It checks whether
    * the given types correlate to each other by Method Invocation Conversion
    * rules. <br>
    * See: https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.3
    * as a reference.
    * 
    * @param that the type the method definition has
    * @param other the type the method is called with
    * @return true, if the types correlate after Method Invocation Conversion
    *         rules. False otherwise.
    */
   private boolean isMethodInvocationConversionCompatible(final ITypeBinding that, final ITypeBinding other) {
      
      return that.isEqualTo(other) 
            || isWideningPrimitiveConversionCompatible(that, other) 
            || isWideningReferenceConversionCompatible(that, other);
   }

   /**
    * Helper Method. Checks if the {@code other} type is a sub type of the
    * {@code that} type. See:
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.5
    * 
    * @param that the type the method definition has
    * @param other the type the method is called with
    * @return true, if {@code other} is a sub type of {@code that}. False
    *         otherwise.
    */
   private boolean isWideningReferenceConversionCompatible(final ITypeBinding that, final ITypeBinding other) {
      ITypeBinding cother = other;
      
      if(that == null || that.isPrimitive()) {        
         return false;
      }
      if(other == null) {
         return false;
      }
      // if the calling type is the null type we return true, because null can be any type.
      if(other.isNullType()) {
         return true;
      }
      if(other.isPrimitive()) {
         cother = boxPrimitiveType(other);
      }
      if(cother == null) {
         return false;
      }

      // get lists, so we don't check interfaces multiple times
      final ArrayList<ITypeBinding> checked = new ArrayList<>();
      final ArrayList<ITypeBinding> leftToCheck = new ArrayList<>();

      // Check Super classes and gather interfaces on the way
      for(ITypeBinding current = cother; current != null; current = current.getSuperclass()) {

         if(current.isEqualTo(that)) {
            return true;
         }

         for(final ITypeBinding i : current.getInterfaces()) {
            if(!leftToCheck.contains(i)) {
               leftToCheck.add(i);
            }
         }
      }

      // check gathered interfaces
      while(leftToCheck.size() > 0) {
         final ITypeBinding i = leftToCheck.get(0);

         if(i.isEqualTo(that)) {
            return true;
         }

         checked.add(i);
         leftToCheck.remove(i);

         for(final ITypeBinding j : i.getInterfaces()) {
            if(!leftToCheck.contains(j) && !checked.contains(j)) {
               leftToCheck.add(j);
            }
         }
      }

      return false;
   }

   /**
    * Helper Method. Checks if the {@code other} type can be extended to the
    * {@code that} type. See:
    * https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.2
    * 
    * @param that the type the method definition has
    * @param other the type the method is called with
    * @return true, if {@code other} can be extended to {@code that}. False
    *         otherwise.
    */
   private boolean isWideningPrimitiveConversionCompatible(final ITypeBinding that, final ITypeBinding other) {
      ITypeBinding cother = other;
      ITypeBinding cthat = that;
      
      if(that == null) {        
         return false;
      }
      if(other == null) {
         return false;
      }
      
      if(!other.isPrimitive()) {
         cother = unboxPrimitiveType(other);
      }
      if(!that.isPrimitive()) {
         cthat = unboxPrimitiveType(that);
      }
      
      if(cother == null || cthat == null) {
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
      
      if(thatName.equals(otherName)) {
         return true;
      }
      
      if(otherName.equals(bYTE)
            && (thatName.equals(sHORT) 
                  || thatName.equals(iNT) 
                  || thatName.equals(lONG) 
                  || thatName.equals(fLOAT) 
                  || thatName.equals(dOUBLE))) {
         return true;
      }

      if(otherName.equals(sHORT) 
            && (thatName.equals(iNT) 
                  || thatName.equals(lONG) 
                  || thatName.equals(fLOAT) 
                  || thatName.equals(dOUBLE))) {
         return true;
      }

      if(otherName.equals(cHAR) 
            && (thatName.equals(iNT) 
                  || thatName.equals(lONG) 
                  || thatName.equals(fLOAT) 
                  || thatName.equals(dOUBLE))) {
         return true;
      }

      if(otherName.equals(iNT) 
            && (thatName.equals(lONG) 
                  || thatName.equals(fLOAT) 
                  || thatName.equals(dOUBLE))) {
         return true;
      }

      if(otherName.equals(lONG) 
            && (thatName.equals(fLOAT) 
                  || thatName.equals(dOUBLE))) {
         return true;
      }

      if(otherName.equals(fLOAT) && thatName.equals(dOUBLE)) {
         return true;
      }

      return false;
   }

   /** Performs unboxing of primitive types.
    * See: https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.8
    * 
    * @param other the {@link ITypeBinding} to be unboxed.
    * @return the {@link ITypeBinding} of the unboxed type or null if the type
    *         can not be unboxed.
    */
   private ITypeBinding unboxPrimitiveType(final ITypeBinding other) {
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Boolean"))) {
         return context.getAST().resolveWellKnownType("boolean");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Byte"))) {
         return context.getAST().resolveWellKnownType("byte");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Short"))) {
         return context.getAST().resolveWellKnownType("short");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Character"))) {
         return context.getAST().resolveWellKnownType("char");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Integer"))) {
         return context.getAST().resolveWellKnownType("int");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Long"))) {
         return context.getAST().resolveWellKnownType("long");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Float"))) {
         return context.getAST().resolveWellKnownType("float");
      }
      if(other.isEqualTo(context.getAST().resolveWellKnownType("java.lang.Double"))) {
         return context.getAST().resolveWellKnownType("double");
      }
      return null;
   }

   /** Performs boxing of primitive types.
    * See: https://docs.oracle.com/javase/specs/jls/se7/html/jls-5.html#jls-5.1.7
    * 
    * @param other the {@link ITypeBinding} to be boxed.
    * @return the {@link ITypeBinding} of the boxed type or null if the type can
    *         not be boxed.
    */
   private ITypeBinding boxPrimitiveType(final ITypeBinding other) {
      if(other.getQualifiedName().equals("boolean")) {
         return context.getAST().resolveWellKnownType("java.lang.Boolean");
      }
      if(other.getQualifiedName().equals("byte")) {
         return context.getAST().resolveWellKnownType("java.lang.Byte");
      }
      if(other.getQualifiedName().equals("short")) {
         return context.getAST().resolveWellKnownType("java.lang.Short");
      }
      if(other.getQualifiedName().equals("char")) {
         return context.getAST().resolveWellKnownType("java.lang.Character");
      }
      if(other.getQualifiedName().equals("int")) {
         return context.getAST().resolveWellKnownType("java.lang.Integer");
      }
      if(other.getQualifiedName().equals("long")) {
         return context.getAST().resolveWellKnownType("java.lang.Long");
      }
      if(other.getQualifiedName().equals("float")) {
         return context.getAST().resolveWellKnownType("java.lang.Float");
      }
      if(other.getQualifiedName().equals("double")) {
         return context.getAST().resolveWellKnownType("java.lang.Double");
      }
      return null;
   }

   private boolean isMoreSpecific(final IMethodBinding m1, final IMethodBinding m2) {
      final ITypeBinding[] types1 = m1.getParameterTypes();
      final ITypeBinding[] types2 = m2.getParameterTypes();
      if(types1.length != types2.length || types1.length == 0) {
         return false;
      }
      for(int i = 0; i < types1.length; i++) {
         if(!types1[i].isEqualTo(types2[i]) && !types1[i].isSubTypeCompatible(types2[i])) {
            return false;
         }
      }
      return true;
   }

   /** Gets the {@link ITypeBinding}s of the given {@link IASTNode}s from the
    * {@link JMLTypeComputer}.
    * 
    * @param parameters the {@link IASTNode}s to check
    * @return an array of {@link ITypeBinding}s corresponding to the given
    *         parameter list
    * @throws ResolverException
    *            if the {@link JMLTypeComputer} throws a
    *            {@link TypeComputerException}.
    */
   private ITypeBinding[] getTypeBindings(final List<IASTNode> parameters) throws ResolverException {
      // if the parameter list is empty, return an empty array
      if(parameters.size() == 0) {
         return new ITypeBinding[0];
      }

      // create an array that can hold the results
      final ITypeBinding[] result = new ITypeBinding[parameters.size()];

      // get a typeComputer
      final JMLTypeComputer tc = new JMLTypeComputer(compilationUnit);

      // save the computed types into the array
      for(int i = 0; i < parameters.size(); i++) {
         try {
            result[i] = tc.computeType(parameters.get(i));
         } catch(final TypeComputerException e) {
            throw new ResolverException("TypeComputer threw an exception when trying to compute the type of a method parameter.", originalNode, e);
         }
      }
      return result;
   }

   /** Checks if the chain of strings we have to resolve is actually a Package
    * rather than Fields/ MemberAccess.
    * 
    * @param resolveString the current String we want to resolve.
    * @return an {@link ASTNode} of the class we found or null if none could be
    *         found.
    */
   private ASTNode findNextReferencesClass(final String resolveString) {

      final IJavaProject javaProject = compilationUnit.getJavaProject();

      final LinkedList<ResolverTask> tasksToWorkWith = new LinkedList<ResolverTask>();
      tasksToWorkWith.addAll(tasks);

      final LinkedList<IType> result = new LinkedList<IType>();
      final SearchEngine se = new SearchEngine();

      String packToSearch = resolveString;
      String classToSearch = "";
      int tasksToRemove = 0;

      while(tasksToWorkWith.size() > 0 && result.size() == 0) {

         classToSearch = tasksToWorkWith.removeFirst().resolveString;

         try {
            se.searchAllTypeNames(packToSearch.toCharArray(), SearchPattern.R_EXACT_MATCH, classToSearch.toCharArray(), SearchPattern.R_EXACT_MATCH,
                  IJavaSearchConstants.CLASS, SearchEngine.createJavaSearchScope(new IJavaElement[]{ javaProject }), new TypeNameMatchRequestor() {
                     @Override
                     public void acceptTypeNameMatch(final TypeNameMatch match) {
                        result.add(match.getType());
                     }
                  }, IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH, new NullProgressMonitor());
         } catch(final JavaModelException e) {
            return null;
         }

         packToSearch = packToSearch + "." + classToSearch;
         tasksToRemove++;
      }

      if(result.size() > 0) {
         final IType type = result.getFirst();

         for(int i = tasksToRemove; i > 0; i--) {
            if(i == 1) {
               final ResolverTask taskFoundClass = tasks.removeFirst();
               currentTask = taskFoundClass;
            } else {
               tasks.removeFirst();
            }
         }

         ASTNode node = null;

         if(type.getClassFile() != null) {
            node = JDTUtil.parse(type.getClassFile());
         } else if(type.getCompilationUnit() != null) {
            node = JDTUtil.parse(type.getCompilationUnit());
         }

         return getTypeInCompilationUnit(classToSearch, node);
      }

      return null;
   }

   /** Finds the {@link MethodDeclaration} corresponding to the given {@link IMethod}.
    * 
    * @param context the context to find the {@link MethodDeclaration} in.
    * @param method the {@link IMethod} to search for.
    * @return the {@link MethodDeclaration} or {@code null} if nothing has been
    *         found.
    */
   private MethodDeclaration findIMethod(final ASTNode context, final IMethod method) {
      if(method == null || context == null) {
         return null;
      }

      final LinkedList<MethodDeclaration> result = new LinkedList<MethodDeclaration>();

      final String[] expectedParameterKeys = Signature.getParameterTypes(method.getKey());

      context.accept(new ASTVisitor() {
         @Override
         public boolean visit(final MethodDeclaration node) {
            if(node.getName().getIdentifier().equals(method.getElementName())) {
               final String[] actualParameterKeys = Signature.getParameterTypes(node.resolveBinding().getKey());
               if(actualParameterKeys.length == expectedParameterKeys.length) {

                  for(int i = 0; i < actualParameterKeys.length; i++) {
                     if(!actualParameterKeys[i].equals(expectedParameterKeys[i])) {
                        return true;
                     } else {
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

      if(result.isEmpty()) {
         return null;
      }

      return result.poll();
   }

   /**
    * Uses the {@link SearchEngine} to get the class specified by resolveString.
    * 
    * @param resolveString the class name you are searching for
    * @param packageName the name of the package that is used as a context to search in
    * @return the {@link ASTNode} of the {@link TypeDeclaration} of the class we
    *         are searching for
    */
   private ASTNode findInPackage(final String resolveString, final String packageName) {
      final SearchEngine se = new SearchEngine();
      final LinkedList<IType> result = new LinkedList<IType>();

      try {
         se.searchAllTypeNames(packageName.toCharArray(), SearchPattern.R_EXACT_MATCH, resolveString.toCharArray(), SearchPattern.R_EXACT_MATCH,
               IJavaSearchConstants.TYPE, SearchEngine.createJavaSearchScope(new IJavaElement[]{ compilationUnit.getJavaProject() }),
               new TypeNameMatchRequestor() {
                  @Override
                  public void acceptTypeNameMatch(final TypeNameMatch match) {
                     result.add(match.getType());
                  }
               }, IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH, new NullProgressMonitor());
      } catch(final JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }

      ASTNode node = null;

      if(result.size() > 0) {
         final IType type = result.getFirst();

         if(type.getClassFile() != null) {
            node = JDTUtil.parse(type.getClassFile());
         } else if(type.getCompilationUnit() != null) {
            node = JDTUtil.parse(type.getCompilationUnit());
         }
      } else {
         return null;
      }

      return getTypeInCompilationUnit(resolveString, node);
   }

   /**
    * Uses the {@link SearchEngine} to get the class specified by resolveString.
    * 
    * @param resolveString
    *           the class name you are searching for
    * @param binding
    *           the {@link IPackageBinding} of the package that is used as a
    *           context to search in
    * @return the {@link ASTNode} of the {@link TypeDeclaration} of the class we
    *         are searching for
    */
   private ASTNode findInPackage(final String resolveString, final IPackageBinding binding) {
      final SearchEngine se = new SearchEngine();
      final LinkedList<IType> result = new LinkedList<IType>();

      try {
         se.searchAllTypeNames(
               binding.getName().toCharArray(), 
               SearchPattern.R_EXACT_MATCH, 
               resolveString.toCharArray(),
               SearchPattern.R_EXACT_MATCH, 
               IJavaSearchConstants.TYPE,
               SearchEngine.createJavaSearchScope(new IJavaElement[]{ binding.getJavaElement() }), 
               new TypeNameMatchRequestor() {
                  @Override
                  public void acceptTypeNameMatch(final TypeNameMatch match) {
                     result.add(match.getType());
                  }
               }, 
               IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH, 
               new NullProgressMonitor());
      } catch(final JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }

      ASTNode node = null;

      if(result.size() > 0) {
         final IType type = result.getFirst();

         if(type.getClassFile() != null) {
            node = JDTUtil.parse(type.getClassFile());
         } else if(type.getCompilationUnit() != null) {
            node = JDTUtil.parse(type.getCompilationUnit());
         }
      } else {
         return null;
      }

      return getTypeInCompilationUnit(resolveString, node);
   }

   /**
    * Gets the {@link TypeDeclaration} with the given name.
    * 
    * @param name
    *           the name of the type we are searching for.
    * @param node
    *           the context we are searching in.
    * @return the {@link TypeDeclaration} or {@code null} if nothing has been
    *         found.
    */
   private TypeDeclaration getTypeInCompilationUnit(final String name, final ASTNode node) {
      final LinkedList<TypeDeclaration> endResult = new LinkedList<TypeDeclaration>();

      if(node != null && name != null) {
         node.accept(new ASTVisitor() {
            @Override
            public boolean visit(final TypeDeclaration node) {
               if(node.getName().getIdentifier() != null && node.getName().getIdentifier().equals(name)) {
                  // We found it. Stop searching.
                  endResult.add(node);
                  return false;
               }
               return true;
            }
         });
      }
      return endResult.poll();
   }

   /**
    * Method to calculate the new context. It checks the last resolved result
    * and sets its type to the new context to search in.
    * 
    * @return the {@link TypeDeclaration} that corresponds to the type that is
    *         the new context or the context that was set before the call if
    *         there was no last result.
    * @throws ResolverException
    *            if the last result points to a primitive type that can not have
    *            members.
    */
   private ASTNode setNewContext() throws ResolverException {
      // If there is no last result, we don't change the context.
      if(currentTask.lastResult == null) {
         return context;
      }

      // get the last result and get its type.
      final ITypeBinding typeBinding = currentTask.lastResult.getReturnType();

      // START testing what the new context might be
      if(typeBinding.isTypeVariable()) {
         // set a boolean to true so we know that we have to search inside
         // the type bounds next time
         currentTask.isTypeVariable = true;
         return context;
         
      } else if(typeBinding.isPrimitive()) {
         throw new ResolverException("Can not resolve an access to a primitive type.", originalNode, null);

      } else if(typeBinding.isArray()) {

         // if we find an array as the context to call something we set a special flag
         // so we can look out for the length field and set the context to object as most
         // of it's method are from there.
         currentTask.isArray = true;
         
         // clone() Method has this return value: 
         // This a special case like "length". It can be found through Object though.
         // So we test for it at the end like we do for "length"
         currentTask.originalTypeBinding = typeBinding;

         return findASTNodeFromType(context.getAST().resolveWellKnownType("java.lang.Object"));

      } else if(typeBinding.isParameterizedType()) {
         
         // Save Type Parameters
         final ITypeBinding newTypeBinding = saveTypeArguments(typeBinding);

         return findASTNodeFromType(newTypeBinding);
      } else {
         return findASTNodeFromType(typeBinding);
      }
   }

   /** Saves the type arguments into a Map in the current Task.
    * 
    * @param typeBinding the {@link ITypeBinding} of the parameterized type.
    * @return the generic {@link ITypeBinding} of the input, or the typeBinding itself, if the input was not parameterized.
    */
   private ITypeBinding saveTypeArguments(final ITypeBinding typeBinding) {
      if(!typeBinding.isParameterizedType()) {
         return typeBinding;
      }
      final ITypeBinding newTypeBinding = typeBinding.getErasure();

      final ITypeBinding[] generic = newTypeBinding.getTypeParameters();
      final ITypeBinding[] specified = typeBinding.getTypeArguments();
      
      for(int i = 0; i < generic.length; i++) {
         currentTask.typeArguments.put(generic[i].getKey(), specified[i]);
      }
      return newTypeBinding;
   }

   /** Helper Method. Gets the {@link TypeDeclaration} corresponding to the Type the 
    *  {@link ITypeBinding} is pointing to. 
    * @param binding 
    *             the {@link ITypeBinding} to get the {@link TypeDeclaration} from
    * @return the {@link TypeDeclaration} of the type the {@link ITypeBinding} is pointing to 
    *             or {@code null} if the given parameter is {@code null} or the type was not found.
    */
   private TypeDeclaration findASTNodeFromType(final ITypeBinding binding) {
      if(binding == null) {
         return null;
      }
      final IType type;
      try {
         type = compilationUnit.getJavaProject().findType(binding.getQualifiedName());
      } catch(final JavaModelException e) {
         LogUtil.getLogger().logError(e);
         return null;
      }
      ASTNode node = null;
      if(type.getClassFile() != null) {
         node = JDTUtil.parse(type.getClassFile());
      } else if(type.getCompilationUnit() != null) {
         node = JDTUtil.parse(type.getCompilationUnit());
      }

      return getTypeInCompilationUnit(type.getElementName(), node);
   }

   private ASTNode findInImports(final String resolveString, final List<ImportDeclaration> imports) throws ResolverException {

      for(final ImportDeclaration imp : imports) {

         final IBinding binding = imp.resolveBinding();

         // ***** PackageBinding - OnDemand Packages
         if(binding instanceof IPackageBinding) {
            if(currentTask.isMethod) {
               continue;
            }
            final ASTNode result = findInPackage(resolveString, (IPackageBinding) binding);
            if(result == null) {
               continue;
            } else {
               return result;
            }

            // ***** TypeBinding - class imports
         } else if(binding instanceof ITypeBinding) {
            if(currentTask.isMethod) {
               continue;
            }
            IType type = null;
            try {
               type = compilationUnit.getJavaProject().findType(((ITypeBinding) binding).getQualifiedName());
               if(type == null || !type.getElementName().equals(resolveString)) {
                  continue;
               }

               ASTNode node = null;

               if(type.getClassFile() != null) {
                  node = JDTUtil.parse(type.getClassFile());
               } else if(type.getCompilationUnit() != null) {
                  node = JDTUtil.parse(type.getCompilationUnit());
               }

               return getTypeInCompilationUnit(resolveString, node);
            } catch(final JavaModelException e) {
               LogUtil.getLogger().logError(e);
               continue;
            }

            // Static Method Import
         } else if(binding instanceof IMethodBinding) {
            if(!currentTask.isMethod || currentTask.isClass) {
               continue;
            }
            IType type = null;
            try {
               type = compilationUnit.getJavaProject().findType(((IMethodBinding) binding).getDeclaringClass().getQualifiedName());

               final IMethodBinding mb = (IMethodBinding) binding;
               if(type == null || !mb.getName().equals(resolveString)) {
                  continue;
               }
               final LinkedList<MethodDeclaration> result = new LinkedList<MethodDeclaration>();
               final ASTVisitor methodFinder = new ASTVisitor() {

                  @Override
                  public boolean visit(final MethodDeclaration node) {
                     if(mb.getJavaElement().equals(node.resolveBinding().getJavaElement())) {
                        result.add(node);
                        return false;
                     }
                     return super.visit(node);
                  }
               };

               if(type.getClassFile() != null) {
                  JDTUtil.parse(type.getClassFile()).accept(methodFinder);
               } else if(type.getCompilationUnit() != null) {
                  JDTUtil.parse(type.getCompilationUnit()).accept(methodFinder);
               }
               if(!result.isEmpty()) {
                  return result.poll();
               }

            } catch(final JavaModelException e) {
               LogUtil.getLogger().logError(e);
               return null;
            }

            // Static Variable Imports
         } else if(binding instanceof IVariableBinding) {
            if(currentTask.isClass || currentTask.isMethod) {
               continue;
            }
            IType type = null;
            try {
               type = compilationUnit.getJavaProject().findType(((IVariableBinding) binding).getDeclaringClass().getQualifiedName());

               final IVariableBinding vb = (IVariableBinding) binding;
               if(type == null || !vb.getName().equals(resolveString)) {
                  continue;
               }
               final LinkedList<VariableDeclaration> result = new LinkedList<VariableDeclaration>();

               final ASTVisitor variableFinder = new ASTVisitor() {

                  @Override
                  public boolean visit(final VariableDeclarationFragment node) {
                     if(vb.getJavaElement().equals(node.resolveBinding().getJavaElement())) {
                        result.add(node);
                        return false;
                     }
                     return super.visit(node);
                  }
               };

               if(type.getClassFile() != null) {
                  JDTUtil.parse(type.getClassFile()).accept(variableFinder);
               } else if(type.getCompilationUnit() != null) {
                  JDTUtil.parse(type.getCompilationUnit()).accept(variableFinder);
               }

               if(!result.isEmpty()) {
                  return result.poll();
               }

            } catch(final JavaModelException e) {
               LogUtil.getLogger().logError(e);
               return null;
            }

         } else {
            throw new ResolverException("ImportDeclaration returned an unrecognised IBinding.", originalNode, null);
         }
      }

      return null;
   }

   /**
    * Searches for fields with the given name in the given context.
    * 
    * @param context
    *           is the context this method is searching in. Should be a
    *           {@link TypeDeclaration},
    *           {@link FieldDeclaration} or {@link VariableDeclarationFragment}
    * @param name
    *           is the name of the identifier we are searching for
    * @return the {@link ASTNode} corresponding to the name in the given context
    */
   private ASTNode findField(final ASTNode context, final String name) {

      if(context == null || name == null) {
         return null;
      }

         // TYPE DECLERATION
      if(context instanceof TypeDeclaration) {
         if(((TypeDeclaration) context).getName().getIdentifier().equals(name)) {
            return context;
         }

         for(final FieldDeclaration field : ((TypeDeclaration) context).getFields()) {
            final ASTNode result = findField(field, name);
            if(result != null) {
               return result;
            }
         }

         // FIELD DECLERATION
      } else if(context instanceof FieldDeclaration) {
         for(final Object fragment : ((FieldDeclaration) context).fragments()) {
            final ASTNode result = findField((VariableDeclarationFragment) fragment, name);
            if(result != null) {
               return result;
            }
         }

         // VariableDeclarationFragment
      } else if(context instanceof VariableDeclarationFragment) {
         if(((VariableDeclarationFragment) context).getName().getIdentifier().equals(name)) {
            return context;
         }
      }
      // NOTHING FOUND
      return null;
   }

   /**
    * Searches for parameters with the given name in the given context.
    * 
    * @param context
    *           is the context this method is searching in. Should be a
    *           {@link MethodDeclaration}
    * @param name
    *           is the name of the identifier we are searching for
    * @return the {@link ASTNode} corresponding to the name in the given context
    */
   private ASTNode findParameters(final ASTNode context, final String name) {

      if(context == null || name == null) {
         return null;
      }

      if(context instanceof MethodDeclaration) {
         if(!((MethodDeclaration) context).isConstructor()) {
            for(final Object parameter : ((MethodDeclaration) context).parameters()) {
               final ASTNode result = findParameters((ASTNode) parameter, name);
               if(result != null) {
                  return result;
               }
            }
         }
         // SingleVariableDeclaration
      } else if(context instanceof SingleVariableDeclaration) {
         if(((SingleVariableDeclaration) context).getName().getIdentifier().equals(name)) {
            return context;
         }
      }
      return null;
   }

   /**
    * Resolves the binding of the given {@link ASTNode} if possible.
    * 
    * @param jdtNode
    *           - the {@link ASTNode} we try to resolve the binding for
    * @return the {@link IBinding} if it was possible to be resolved, null
    *         otherwise
    */
   private IBinding resolveBinding(final ASTNode jdtNode) {
      IBinding binding = null;

      if(jdtNode instanceof TypeDeclaration) {
         binding = ((TypeDeclaration) jdtNode).resolveBinding();
      } else if(jdtNode instanceof MethodDeclaration) {
         binding = ((MethodDeclaration) jdtNode).resolveBinding();
      } else if(jdtNode instanceof SingleVariableDeclaration) {
         binding = ((SingleVariableDeclaration) jdtNode).resolveBinding();
      } else if(jdtNode instanceof VariableDeclarationFragment) {
         binding = ((VariableDeclarationFragment) jdtNode).resolveBinding();
      } else if(jdtNode instanceof Type) {
         binding = ((Type) jdtNode).resolveBinding();
      }
      return binding;
   }

   /**
    * Get the {@link ResolveResultType} for the given {@link ASTNode}.
    * 
    * @param jdtNode
    *           - the {@link ASTNode}
    * @return a {@link ResolveResultType}. It has the value {@code UNSPECIFIED}
    *         if the type could not be found.
    */
   private ResolveResultType getResolveType(final ASTNode jdtNode) {
      ResolveResultType resultType = ResolveResultType.UNSPECIFIED;

      if(jdtNode instanceof TypeDeclaration) {
         resultType = ResolveResultType.CLASS;
      } else if(jdtNode instanceof MethodDeclaration) {
         resultType = ResolveResultType.METHOD;
      } else if(jdtNode instanceof SingleVariableDeclaration) {
         resultType = ResolveResultType.PARAMETER;
      } else if(jdtNode instanceof VariableDeclarationFragment) {
         resultType = ResolveResultType.FIELD;
      }
      return resultType;
   }

   /**
    * Builds the {@link ResolverTask} list.
    * 
    * @param jmlNode
    *           - the {@link IASTNode} that is supposed to be resolved.
    * @throws ResolverException
    *            is thrown, if the jmlNode isn't built correctly.
    */
   protected final void buildResolverTask(final IASTNode jmlNode) throws ResolverException {

      tasks.add(new ResolverTask());

      try {
         // This calls all the functions that build the resolver task list.
         // it's either a String (as in some assignable clauses or when the typeComputer
         // calls the resolver to resolve a type name) or it is a primary expression,
         // when called from a normal source that tries to resolve fields or methods.
         final boolean result = isReferenceType(jmlNode) || isString(jmlNode) || isPrimaryExpr(jmlNode);
         if(result == false) {
            throw new ResolverException("Given IASTNode is not resolvable/ not supported.", originalNode, null);
         }

      } catch(final NullPointerException e) {
         throw new ResolverException("Given IASTNode is not resolvable. " 
               + "A NullPointerException occured while trying to access children.", originalNode,  e);
      }

   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code PRIMARY_EXPR}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isPrimaryExpr(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
         // PRIMARY
         final IASTNode firstChildren = node.getChildren().get(0);
         if(!isPrimaryExpr(node.getChildren().get(0))) {
            // Primaries may be cascaded.
            result = isIdentifier(firstChildren) || isJmlPrimary(firstChildren) || isJavaKeyword(firstChildren) || isCast(firstChildren);
         }
         // Process the Children of the Node
         if(node.getChildren().size() > 1) {
            result = isList(node.getChildren().get(1));
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code JAVA_KEYWORD}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isJavaKeyword(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.JAVA_KEYWORD) {
         tasks.getLast().isKeyword = true;
         result = isString(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code JML_PRIMARY}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isJmlPrimary(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.JML_PRIMARY) {
         // PRIMARY -> JML_PRIMARY
         result = isKeyword(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type {@link NodeTypes}.
    * {@code KEYWORD}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isKeyword(final IASTNode node) {
      boolean result = false;
      if(node.getType() == NodeTypes.KEYWORD && ((IKeywordNode) node).getKeywordInstance().equals("\\result")) {
         // PRIMARY -> JML_PRIMARY -> []
         tasks.getLast().isKeyword = true;
         tasks.getLast().resolveString = ((IKeywordNode) node).getKeywordInstance();

         result = true;
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code IDENTIFIER}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isIdentifier(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.IDENTIFIER) {
         // PRIMARY -> IDENTIFIER
         result = isString(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type {@link NodeTypes}.
    * {@code STRING}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isString(final IASTNode node) {
      boolean result = false;
      if(node.getType() == NodeTypes.STRING) {
         // PRIMARY -> IDENTIFIER -> STRING
         tasks.getLast().resolveString = ((IStringNode) node).getString();
         tasks.getLast().node = (IStringNode) node;
         result = true;
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type {@link NodeTypes}.
    * {@code LIST}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isList(final IASTNode node) {
      boolean result = false;
      if(node.getType() == NodeTypes.LIST) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST
         for(final IASTNode child : node.getChildren()) {
            result = isMethodCall(child) || isMemberAccess(child) || isArrayAccess(child);
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code ARRAY_ACCESS}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isArrayAccess(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.ARRAY_ACCESS) {
         // PRIMARY -> []
         // -> LIST -> ARRAY_ACCESS
         final IStringNode save = tasks.getLast().node;
         
         tasks.add(new ResolverTask());
         tasks.getLast().isArrayAcess = true;
         tasks.getLast().node = save;
         result = true;
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code METHOD_CALL_PARAMETERS}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isMethodCall(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST -> METHOD_CALL
         tasks.getLast().isMethod = true;

         result = isExpressionList(node.getChildren().get(0)) || isEmptyList(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type {@link NodeTypes}.
    * {@code NONE}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isEmptyList(final IASTNode node) {
      // PRIMARY -> IDENTIFIER -> STRING
      // -> LIST -> METHOD_CALL -> NONE
      return node.getType() == NodeTypes.NONE;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code EXPRESSION_LIST}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isExpressionList(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.EXPRESSION_LIST) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST -> METHOD_CALL -> EXPRESSION_LIST
         for(final IASTNode child : node.getChildren()) {
            tasks.getLast().parameters.add(child);
            result = true;
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code MEMBER_ACCESS}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isMemberAccess(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.MEMBER_ACCESS) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST -> MEMBER_ACCESS
         tasks.add(new ResolverTask());
         tasks.getLast().node = (IStringNode) node.getChildren().get(1);
         tasks.getLast().resolveString = tasks.getLast().node.getString();
         result = true;
      }

      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be
    * called on an {@link IASTNode} that has the type
    * {@link ExpressionNodeTypes}.{@code CAST}
    * 
    * @param node
    *           - the {@link IASTNode} to get information from.
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isCast(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.CAST) {
         if(node.getChildren().size() > 0) {
            result = isReferenceType(node.getChildren().get(0));
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It is needed
    * when a cast expression is needed to be resolved, i.e. to find out to which
    * class some object is casted to.
    * 
    * @param node
    *           - the {@link IASTNode} to get information from.
    * @return true, if the node and every child node is correct.
    */
   protected final boolean isReferenceType(final IASTNode node) {
      boolean result = false;
      if(node.getType() == ExpressionNodeTypes.REFERENCE_TYPE) {
         result = true;
         // Such a node type is build like this
         // ReferenceType(Name(String, String, String,...))
         // More than one String is used when the cast goal is fully
         // qualified like (java.lang.String)
         final List<IASTNode> children = node.getChildren().get(0).getChildren();
         for(int i = 0; i < children.size(); i++) {
            tasks.getLast().isClass = true;
            isString(children.get(i));
            // add a new task for the next String if there is still one more
            // String
            if(i + 1 < children.size()) {
               tasks.add(new ResolverTask());
            }
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final boolean hasNext() {
      return tasks.size() > 0 ? true : false;
   }

   /**
    * Uses the TypeComputer to find out what the ITypeBinding of the parameters
    * are then creates the Signature of those Bindings.
    * 
    * @param parameters
    *           the List of the parameters
    * @return a String array containing the signatures of the parameter types in
    *         the same order.
    * @throws ResolverException
    *            if the TypeComputer can not compute the parameter type.
    */
   /*
    * private String[] createParameterSignatures(final List<IASTNode>
    * parameters) throws ResolverException { if(parameters.size() == 0) { return
    * new String[0]; }
    * 
    * final String[] result = new String[currentTask.parameters.size()];
    * 
    * for(int i = 0; i < currentTask.parameters.size(); i++) { final
    * JMLTypeComputer tc = new JMLTypeComputer(compilationUnit);
    * 
    * ITypeBinding b = null; try { b =
    * tc.computeType(currentTask.parameters.get(i)); } catch (final
    * TypeComputerException e) { throw new ResolverException(
    * "TypeComputer threw an exception when trying to resolve a method parameter."
    * , e); } if(b != null) { result[i] =
    * Signature.createTypeSignature(b.getQualifiedName(), true); } }
    * 
    * return result; }
    */

}
