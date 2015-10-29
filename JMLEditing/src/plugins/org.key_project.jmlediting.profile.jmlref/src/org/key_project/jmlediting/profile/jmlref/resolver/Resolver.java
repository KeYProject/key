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
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTMatcher;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Block;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.ForStatement;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.IPackageBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.ImportDeclaration;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.PackageDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.SwitchStatement;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.TypeParameter;
import org.eclipse.jdt.core.dom.VariableDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.core.dom.WhileStatement;
import org.eclipse.jdt.core.search.IJavaSearchConstants;
import org.eclipse.jdt.core.search.SearchEngine;
import org.eclipse.jdt.core.search.SearchPattern;
import org.eclipse.jdt.core.search.TypeNameMatch;
import org.eclipse.jdt.core.search.TypeNameMatchRequestor;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * The Resolver class, that only has three public methods. <br>
 * "{@link #resolve(ICompilationUnit, IASTNode) -> {@link ResolveResult}" will
 * resolve the given {@link IASTNode} and find the corresponding JavaElement or JML
 * declaration <br>
 * "{@link #next()} -> {@link ResolveResult}" will resolve any member access that is appended
 * to the original identifier. <br>
 * "{@link #hasNext()} -> boolean" that will return true, if the taskList is not empty and
 * there is still something to resolve with the {@link #next()} method.
 * 
 * @author Christopher Beckmann
 * @see {@link TaskBuilder}
 * @see {@link ResolverTask}
 */
public class Resolver implements IResolver {

   private ASTNode context = null;
   private ICompilationUnit compilationUnit = null;
   private final Map<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();
   private final List<ImportDeclaration> imports = new ArrayList<ImportDeclaration>();
   private final List<ImportDeclaration> onDemandImports = new ArrayList<ImportDeclaration>();
   private LinkedList<ResolverTask> tasks = new LinkedList<ResolverTask>();
   private ResolverTask currentTask = null;
   private PackageDeclaration pack = null;
   private IASTNode originalNode = null;
   private int skipIdentifier = 0;

   /**
    * {@inheritDoc}
    */
   @Override
   public final ResolveResult resolve(final ICompilationUnit compilationUnit, final IASTNode jmlNode) throws ResolverException {

      // Valid call ?
      if (jmlNode == null || compilationUnit == null) {
         return null;
      }

      // reset everything .. so we can resolve more than once, with one instance of a resolver
      reset(compilationUnit, jmlNode);

      // First, we get all the information about what we have to resolve by checking the given IASTNode.
      // this builds up the task list.
      tasks = new TaskBuilder().buildResolverTask(jmlNode);

      // Gather information about the current CompilationUnit
      // Parse JDT first
      final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(compilationUnit);

      // Save the package information and the import declarations
      pack = jdtAST.getPackage();

      // split the list because we have to check for direct imports first
      @SuppressWarnings("unchecked")
      final List<ImportDeclaration> importList = jdtAST.imports();
      for (final ImportDeclaration i : importList) {
         if (i.isOnDemand()) {
            onDemandImports.add(i);
         }
         else {
            imports.add(i);
         }
      }

      // Get the context information. That is the ASTNode to which the JML node refers to / belongs to.
      context = new SearchContextMapper(compilationUnit, jdtAST).getSearchContext(jmlNode);

      return next();
   }

   /**
    * Reset the ResolverTask to its default values.
    * 
    * @param compilationUnit the {@link ICompilationUnit} to reset to.
    * @param jmlNode the {@link IASTNode} the resolver was called with
    */
   private void reset(final ICompilationUnit compilationUnit, final IASTNode jmlNode) {
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
      originalNode = jmlNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final ResolveResult next() throws ResolverException {

      
      // Get the task to do - if there is any left.
      currentTask = tasks.poll();
      if (currentTask == null) {
         return null;
      }

      // Initialize the return values
      ASTNode jdtNode = null;
      IBinding binding = null;
      ITypeBinding returnValue = null;
      ResolveResultType resolveResultType = null;

      if (!currentTask.isArrayAcess()) {
         // start processing and searching for the identifier
         if (currentTask.isKeyword()) {
            jdtNode = processKeyword(context);
         }
         else {
            jdtNode = findIdentifier();
         }

         // if we have multiple of the same task in here
         // because we are trying to find something from a TypeParameter
         // we keep on going with the next task instead of returning null
         if (skipIdentifier != 0) {
            if (tasks.peek() != null) {
               if (jdtNode == null) {
                  return next();
               }
               else {
                  // If we found something, we remove the rest of the tasks with our skip
                  // identifier so we can work normally after that
                  final List<ResolverTask> toRemove = new LinkedList<ResolverTask>();
                  for (final ResolverTask t : tasks) {
                     if (t.getSkipIdentifier() == skipIdentifier) {
                        toRemove.add(t);
                     }
                  }
                  // I have to do this like this, because removing an element from the list
                  // above,
                  // will terminate it earlier than I actually want it to.
                  for (final ResolverTask t : toRemove) {
                     tasks.remove(t);
                  }
               }
            }
            // reset skip identifier to either the next task or if its not part 0
            if (tasks.peek() != null) {
               skipIdentifier = tasks.peek().getSkipIdentifier();
            }
         }

         // Are we trying to access functions of a TypeParameter?
         if (jdtNode == null && currentTask.isTypeVariable() || jdtNode instanceof TypeParameter) {

            // We don't know the final types yet. So we get all the type bounds.
            final ITypeBinding[] bounds = jdtNode == null ? currentTask.getLastResult()
                     .getReturnType().getTypeBounds() : 
                     ((TypeParameter) jdtNode).resolveBinding().getTypeBounds();
            // Do we have bounds? If not .. we can not access anything on this type. Because
            // we don't know what type it will be.
            if (bounds.length > 0) {
               // remove the next task and replace it with our versions
               final ResolverTask nextTask = jdtNode == null ? currentTask : tasks.poll();
               ResolveResult result = null;
               final int identifier = nextTask.hashCode();
               skipIdentifier = identifier;
               for (final ITypeBinding t : bounds) {
                  tasks.addFirst(new ResolverTask());
                  tasks.getFirst().setArrayAcess(nextTask.isArrayAcess());
                  tasks.getFirst().setClass(nextTask.isClass());
                  tasks.getFirst().setKeyword(nextTask.isKeyword());
                  tasks.getFirst().setMethod(nextTask.isMethod());
                  tasks.getFirst().setNode(nextTask.getNode());
                  tasks.getFirst().getParameters().addAll(nextTask.getParameters());
                  tasks.getFirst().setResolveString(nextTask.getResolveString());
                  tasks.getFirst().setSkipIdentifier(identifier);
                  result = new ResolveResult(jdtNode, resolveResultType, binding, t, currentTask.getNode());
                  tasks.getFirst().setLastResult(result);
               }
            }
            else {
               // If there is no bound.. set the next context to Object. Those functions are
               // everywhere.
               returnValue = context.getAST().resolveWellKnownType("java.lang.Object");
               currentTask.setTypeVariable(false);
               currentTask.setLastResult(new ResolveResult(currentTask.getLastResult().getJDTNode(), currentTask.getLastResult().getResolveType(), currentTask.getLastResult().getBinding(), returnValue, currentTask.getLastResult().getStringNode()));
               tasks.add(currentTask);
            }
            if (jdtNode == null) {
               return next();
            }
         }

         if (!currentTask.isArray()) {
            if (jdtNode == null) {
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
      }
      else {
         // Array Access
         jdtNode = currentTask.getLastResult().getJDTNode();
         binding = TypeComputer.getTypeFromBinding(currentTask.getLastResult().getBinding())
                  .getComponentType();
         returnValue = TypeComputer.getTypeFromBinding(binding);
         resolveResultType = ResolveResultType.ARRAY_ACCESS;

         if (binding == null) {
            throw new ResolverException("Tried to perform an array access on a non array.", originalNode, null);
         }
      }

      // If we have parameterized types in our result.
      // We have to add the real result as an additional parameter.
      if (currentTask.getTypeArguments().size() > 0) {
         final ITypeBinding value = currentTask.getTypeArguments().get(returnValue.getKey());
         if (value != null) {
            returnValue = value;
         }
      }

      if (currentTask.isArray()) {
         if (currentTask.getResolveString().equals("length")) {
            returnValue = context.getAST().resolveWellKnownType("int");
            final ResolveResult finalResult = new ResolveResult(null, ResolveResultType.ARRAY_LENGTH, returnValue, returnValue, currentTask.getNode());
            return finalResult;
         }
         else if (currentTask.getResolveString().equals("clone")) {
            returnValue = currentTask.getOriginalTypeBinding();
            binding = resolveBinding(jdtNode);
         }
         else {
            // this is a method we can pass on
            binding = resolveBinding(jdtNode);
            returnValue = TypeComputer.getTypeFromBinding(binding);
            resolveResultType = getResolveType(jdtNode);
         }
      }

      final ResolveResult finalResult = new ResolveResult(jdtNode, resolveResultType, binding, returnValue, currentTask.getNode());

      if (tasks.peek() != null && !(jdtNode instanceof TypeParameter)) {
         tasks.peek().setLastResult(finalResult);
      }
      return finalResult;
   }

   // Depending on the keyword, we need to search in different directions / different content.
   private ASTNode processKeyword(final ASTNode context) throws ResolverException {
      if(context == null) {
         return null;
      }
      if (currentTask.isKeyword()) {
         if (currentTask.getResolveString().equals("this")) {
            return getDeclaringClass(context);
         }
         else if (currentTask.getResolveString().equals("super")) {
            return getDeclaringClass(context).getSuperclassType();
         }
         else if (currentTask.getResolveString().equals("\\result")) {
            return findMethodReturnValue(context);
         }
      }
      return null;
   }

   // we traverse the ASTNode to the top, i.e. from child to parent, until we found
   // a type declaration
   private TypeDeclaration getDeclaringClass(final ASTNode context) {
      ASTNode clazz = context;
      while (clazz != null && !(clazz instanceof TypeDeclaration)
               && clazz.getParent() != null) {
         clazz = clazz.getParent();
      }
      return (TypeDeclaration) clazz;
   }

   // returns the returnType of a method or null if it is no method
   private ASTNode findMethodReturnValue(final ASTNode context) throws ResolverException {
      if (context instanceof MethodDeclaration) {
         return ((MethodDeclaration) context).getReturnType2();
      }
      else {
         throw new ResolverException("'\\result' can not be resolved, if the JML comment is not bound to a method", originalNode, null);
      }
   }

   /**
    * Searches for the {@link ASTNode} specified by {@code currentTask}.
    * 
    * @return the {@link ASTNode} or null if it could not be found
    * @throws ResolverException is thrown if the setNewContext, findMethod or findInImports
    *            methods throws a ResolverException
    */
   private ASTNode findIdentifier() throws ResolverException {
      // Initialize jdtNode with null. If this ever changes to something else,
      // we found our node!
      ASTNode jdtNode = null;
      
      // Set the context.
      // Very important method call!
      context = setNewContext();
      if(context == null) {
         return null;
      }

      // is this a type variable?
      // then get to the end part so we can start building ResolveResults
      if (currentTask.isTypeVariable()) {
         return null;
      }

      // start with searching for parameters if we are not searching for a
      // method or a class
      // if lastResult is null, this must be the first call of next() and is
      // the only case we could find parameters in
      if (context instanceof MethodDeclaration && !currentTask.isMethod() && !currentTask.isClass() && !currentTask.isArray()) {
         jdtNode = findParameters(context, currentTask.getResolveString());
      }

      // we need to get more information, in particular which class declared the method/field.
      // if our context is already set to a TypeDeclaration nothing will change.
      // context = getDeclaringClass(context);

      if (jdtNode == null && !currentTask.isMethod() && !currentTask.isClass() && !currentTask.isArray()) {

         ASTNode searchContext = context;

         ASTNode lastChecked;
         do {
            // Check every scope.
            do {
               lastChecked = searchContext;
               
               jdtNode = findField(searchContext, currentTask.getResolveString());
               
               searchContext = getParentSearchContext(searchContext);
               
               
            } while (jdtNode == null && !(lastChecked instanceof TypeDeclaration));
            
            searchContext = getSuperClass(searchContext);
            
         }
         while (jdtNode == null && searchContext != null);
      }
      
      // after this .. we set the context to the class.
      context = getDeclaringClass(context);
      
      // are we searching for a method?
      if (jdtNode == null && currentTask.isMethod()) {

         // TODO: Variable Arity Methods are not supported yet.
         // TODO: Wildcards not supported yet.

         ASTNode searchContext = context;

         do {
            jdtNode = new MethodFinder(searchContext, currentTask, compilationUnit, originalNode).findMethod();
            searchContext = getSuperClass(searchContext);

         }
         while (jdtNode == null && searchContext != null);
      }
      if (jdtNode == null && !currentTask.isArray()) {
         jdtNode = findTypeParameter(context, currentTask.getResolveString());
      }
      if (jdtNode == null && !currentTask.isArray()) {
         jdtNode = findInImports(currentTask.getResolveString(), imports);
      }
      if (jdtNode == null && !currentTask.isArray()) {
         jdtNode = findInPackage(currentTask.getResolveString(), pack.resolveBinding());
      }
      if (jdtNode == null && !currentTask.isArray()) {
         jdtNode = findInImports(currentTask.getResolveString(), onDemandImports);
      }
      if (jdtNode == null && !currentTask.isArray()) {
         jdtNode = findInPackage(currentTask.getResolveString(), "java.lang");
      }
      if (jdtNode == null && !currentTask.isArray()) {
         jdtNode = findNextReferencesClass(currentTask.getResolveString());
      }

      // return what we found... either null or the jdtNode
      return jdtNode;
   }

   private ASTNode getParentSearchContext(final ASTNode searchContext) {
      if(searchContext == null) {
         return null;
      }
      if(searchContext instanceof TypeDeclaration) {
         return searchContext;
      }

      // get the next scope .. if we come by our own TypeDeclaration we stop.
      ASTNode result = searchContext;
      final TypeDeclaration thisType = getDeclaringClass(searchContext);
      do {
         result = result.getParent();
      } while(!(result instanceof Block) && !thisType.subtreeMatch(new ASTMatcher(), result));
      
      return result;
   }

   // we search the context for the node with the given name.
   private ASTNode findTypeParameter(final ASTNode context, final String resolveString) {
      if(context == null) {
         return null;
      }
      final LinkedList<TypeParameter> result = new LinkedList<TypeParameter>();
      context.accept(new ASTVisitor() {

         @Override
         public boolean visit(final TypeParameter node) {
            if (result.size() > 0) {
               return false;
            }
            if (node.getName().getIdentifier().equals(resolveString)) {
               result.add(node);
               return false;
            }
            return true;
         }
      });
      return result.poll();
   }

   /** Returns the super class of the class the given {@link ASTNode} is in.
    * 
    * @param searchContext the {@link ASTNode} to get the super class from
    * @return the {@link TypeDeclaration} of the super class
    */
   private TypeDeclaration getSuperClass(final ASTNode searchContext) {
      if (searchContext == null) {
         return null;
      }
      // Set new context to super class and call it again until we
      // reach Object
      final Type superClass = getDeclaringClass(searchContext).getSuperclassType();
      IType type = null;

      if (superClass == null) {
         // Create a TypeBinding of object to compare
         final ITypeBinding objectTypeBinding = context.getAST().resolveWellKnownType("java.lang.Object");

         if (((TypeDeclaration) searchContext).resolveBinding().isEqualTo(objectTypeBinding)) {
            return null;
         }
         try {
            type = compilationUnit.getJavaProject().findType(objectTypeBinding.getQualifiedName());
         }
         catch (final JavaModelException e) {
            LogUtil.getLogger().logError(e);
         }
      }
      else {
         type = (IType) superClass.resolveBinding().getJavaElement();
      }
      if (type == null) {
         return null;
      }

      ASTNode node = null;
      if (type.getClassFile() != null) {
         node = JDTUtil.parse(type.getClassFile());
      }
      else if (type.getCompilationUnit() != null) {
         node = JDTUtil.parse(type.getCompilationUnit());
      }
      return getTypeInCompilationUnit(type.getElementName(), node);
   }

   /**
    * Checks if the chain of strings we have to resolve is actually a package rather than
    * fields/memberAccess.
    * 
    * @param resolveString the current String we want to resolve.
    * @return an {@link ASTNode} of the class we found or null if none could be found.
    */
   private ASTNode findNextReferencesClass(final String resolveString) {

      final IJavaProject javaProject = compilationUnit.getJavaProject();

      // Get a working copy of the task list because we want to remove the ones we have seen
      final LinkedList<ResolverTask> tasksToWorkWith = new LinkedList<ResolverTask>();
      tasksToWorkWith.addAll(tasks);

      // We use a search engine to find a class with a given name in a given package
      // The strings which needs to be resolved and are stored in the tasks, are combined
      // that the last one is tested as the class name and all before as the package path
      final LinkedList<IType> result = new LinkedList<IType>();
      final SearchEngine se = new SearchEngine();

      final StringBuilder packToSearch = new StringBuilder(resolveString);
      String classToSearch = "";
      int tasksToRemove = 0;

      while (tasksToWorkWith.size() > 0 && result.size() == 0) {

         classToSearch = tasksToWorkWith.removeFirst().getResolveString();

         try {
            se.searchAllTypeNames(packToSearch.toString().toCharArray(),
                     SearchPattern.R_EXACT_MATCH, classToSearch.toCharArray(),
                     SearchPattern.R_EXACT_MATCH, IJavaSearchConstants.CLASS,
                     SearchEngine.createJavaSearchScope(new IJavaElement[] { javaProject }),
                     new TypeNameMatchRequestor() {
                        @Override
                        public void acceptTypeNameMatch(final TypeNameMatch match) {
                           result.add(match.getType());
                        }
                     }, IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH,
                     new NullProgressMonitor());
         }
         catch (final JavaModelException e) {
            return null;
         }

         // the string which we assumed was a class, will next be tested as the last
         // part of the package path
         packToSearch.append(".");
         packToSearch.append(classToSearch);
         tasksToRemove++;
      }

      // Check if we have found some class. It could have ended because no tasks were left
      if (result.size() > 0) {
         final IType type = result.getFirst();

         // We remove all the tasks which were in fact just the path to a class
         for (int i = tasksToRemove; i > 0; i--) {
            if (i == 1) {
               final ResolverTask taskFoundClass = tasks.removeFirst();
               currentTask = taskFoundClass;
            }
            else {
               tasks.removeFirst();
            }
         }

         // We get the class file of the found class and return its type declaration.
         ASTNode node = null;

         if (type.getClassFile() != null) {
            node = JDTUtil.parse(type.getClassFile());
         }
         else if (type.getCompilationUnit() != null) {
            node = JDTUtil.parse(type.getCompilationUnit());
         }

         return getTypeInCompilationUnit(classToSearch, node);
      }

      return null;
   }

   /**
    * Uses the {@link SearchEngine} to get the class specified by resolveString.
    * 
    * @param resolveString the class name you are searching for
    * @param packageName the name of the package that is used as a context to search in
    * @return the {@link ASTNode} of the {@link TypeDeclaration} of the class we are searching
    *         for
    */
   private ASTNode findInPackage(final String resolveString, final String packageName) {
      final SearchEngine se = new SearchEngine();
      final LinkedList<IType> result = new LinkedList<IType>();

      try {
         se.searchAllTypeNames(packageName.toCharArray(), SearchPattern.R_EXACT_MATCH,
                  resolveString.toCharArray(), SearchPattern.R_EXACT_MATCH,
                  IJavaSearchConstants.TYPE, SearchEngine
                           .createJavaSearchScope(new IJavaElement[] { compilationUnit
                                    .getJavaProject() }), new TypeNameMatchRequestor() {
                     @Override
                     public void acceptTypeNameMatch(final TypeNameMatch match) {
                        result.add(match.getType());
                     }
                  }, IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH,
                  new NullProgressMonitor());
      }
      catch (final JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }

      ASTNode node = null;

      if (result.size() > 0) {
         final IType type = result.getFirst();

         if (type.getClassFile() != null) {
            node = JDTUtil.parse(type.getClassFile());
         }
         else if (type.getCompilationUnit() != null) {
            node = JDTUtil.parse(type.getCompilationUnit());
         }
      }
      else {
         return null;
      }

      return getTypeInCompilationUnit(resolveString, node);
   }

   /**
    * Uses the {@link SearchEngine} to get the class specified by resolveString.
    * 
    * @param resolveString the class name you are searching for
    * @param binding the {@link IPackageBinding} of the package that is used as a context to
    *           search in
    * @return the {@link ASTNode} of the {@link TypeDeclaration} of the class we are searching
    *         for
    */
   private ASTNode findInPackage(final String resolveString, final IPackageBinding binding) {
      final SearchEngine se = new SearchEngine();
      final LinkedList<IType> result = new LinkedList<IType>();

      try {
         se.searchAllTypeNames(binding.getName().toCharArray(), SearchPattern.R_EXACT_MATCH,
                  resolveString.toCharArray(), SearchPattern.R_EXACT_MATCH,
                  IJavaSearchConstants.TYPE, SearchEngine
                           .createJavaSearchScope(new IJavaElement[] { binding
                                    .getJavaElement() }), new TypeNameMatchRequestor() {
                     @Override
                     public void acceptTypeNameMatch(final TypeNameMatch match) {
                        result.add(match.getType());
                     }
                  }, IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH,
                  new NullProgressMonitor());
      }
      catch (final JavaModelException e) {
         LogUtil.getLogger().logError(e);
      }

      ASTNode node = null;

      if (result.size() > 0) {
         final IType type = result.getFirst();

         if (type.getClassFile() != null) {
            node = JDTUtil.parse(type.getClassFile());
         }
         else if (type.getCompilationUnit() != null) {
            node = JDTUtil.parse(type.getCompilationUnit());
         }
      }
      else {
         return null;
      }

      return getTypeInCompilationUnit(resolveString, node);
   }

   /**
    * Gets the {@link TypeDeclaration} with the given name inside the given context given as {@code node}.
    * 
    * @param name the name of the type we are searching for.
    * @param node the context we are searching in.
    * @return the {@link TypeDeclaration} or {@code null} if nothing has been found.
    */
   static TypeDeclaration getTypeInCompilationUnit(final String name, final ASTNode node) {
      final LinkedList<TypeDeclaration> endResult = new LinkedList<TypeDeclaration>();

      if (node != null && name != null) {
         node.accept(new ASTVisitor() {
            @Override
            public boolean visit(final TypeDeclaration node) {
               if(endResult.size() > 0) {
                  return false;
               }
               if (node.getName().getIdentifier() != null && node.getName().getIdentifier().equals(name)) {
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
    * Method to calculate the new context. It checks the last resolved result and sets its
    * type to the new context to search in.
    * 
    * @return the {@link TypeDeclaration} that corresponds to the type that is the new context
    *         or the context that was set before the call if there was no last result.
    * @throws ResolverException if the last result points to a primitive type that can not have members.
    */
   private ASTNode setNewContext() throws ResolverException {
      // If there is no last result, we don't change the context.
      if (currentTask.getLastResult() == null) {
         return context;
      }

      // get the last result and get its type.
      final ITypeBinding typeBinding = currentTask.getLastResult().getReturnType();

      // START testing what the new context might be
      if (typeBinding.isTypeVariable()) {
         // set a boolean to true so we know that we have to search inside
         // the type parameter bounds next time
         currentTask.setTypeVariable(true);
         return context;

      }
      else if (typeBinding.isPrimitive()) {
         throw new ResolverException("Can not resolve an access to a primitive type.", originalNode, null);

      }
      else if (typeBinding.isArray()) {

         // if we find an array as the context to call something we set a special flag
         // so we can look out for the length field and set the context to object as most
         // of it's method are from there.
         currentTask.setArray(true);

         // clone() Method has this return value:
         // This a special case like "length". It can be found through Object though.
         // So we test for it at the end like we do for "length"
         currentTask.setOriginalTypeBinding(typeBinding);

         return findASTNodeFromType(context.getAST().resolveWellKnownType("java.lang.Object"));

      }
      else if (typeBinding.isParameterizedType()) {

         // Save Type Parameters
         final ITypeBinding newTypeBinding = saveTypeArguments(typeBinding);

         return findASTNodeFromType(newTypeBinding);
      }
      else {
         return findASTNodeFromType(typeBinding);
      }
   }

   /**
    * Saves the type arguments into a Map in the current Task.
    * 
    * @param typeBinding the {@link ITypeBinding} of the parameterized type.
    * @return the generic {@link ITypeBinding} of the input, or the typeBinding itself, if the
    *         input was not parameterized.
    */
   private ITypeBinding saveTypeArguments(final ITypeBinding typeBinding) {
      if (!typeBinding.isParameterizedType()) {
         return typeBinding;
      }
      final ITypeBinding newTypeBinding = typeBinding.getErasure();

      final ITypeBinding[] generic = newTypeBinding.getTypeParameters();
      final ITypeBinding[] specified = typeBinding.getTypeArguments();

      for (int i = 0; i < generic.length; i++) {
         currentTask.getTypeArguments().put(generic[i].getKey(), specified[i]);
      }
      return newTypeBinding;
   }

   /**
    * Helper Method. Gets the {@link TypeDeclaration} corresponding to the Type the
    * {@link ITypeBinding} is pointing to.
    * 
    * @param binding the {@link ITypeBinding} to get the {@link TypeDeclaration} from
    * @return the {@link TypeDeclaration} of the type the {@link ITypeBinding} is pointing to
    *         or {@code null} if the given parameter is {@code null} or the type was not
    *         found.
    */
   private TypeDeclaration findASTNodeFromType(final ITypeBinding binding) {
      if (binding == null) {
         return null;
      }
      final IType type;
      try {
         type = compilationUnit.getJavaProject().findType(binding.getQualifiedName());
      }
      catch (final JavaModelException e) {
         LogUtil.getLogger().logError(e);
         return null;
      }
      ASTNode node = null;
      if (type.getClassFile() != null) {
         node = JDTUtil.parse(type.getClassFile());
      }
      else if (type.getCompilationUnit() != null) {
         node = JDTUtil.parse(type.getCompilationUnit());
      }

      return getTypeInCompilationUnit(type.getElementName(), node);
   }

   
   private ASTNode findInImports(final String resolveString, final List<ImportDeclaration> imports) throws ResolverException {

      /* The given resolveString could be a class which is explicitly imported
       * or it could be a class which is imported on demand (using the * import).
       * But it could also be the name of a field/ method that was imported directly 
       * with a static import.
       */
      for (final ImportDeclaration imp : imports) {

         final IBinding binding = imp.resolveBinding();

         // ***** PackageBinding - OnDemand Packages
         if (binding instanceof IPackageBinding) {
            if (currentTask.isMethod()) {
               continue;
            }
            final ASTNode result = findInPackage(resolveString, (IPackageBinding) binding);
            if (result == null) {
               continue;
            }
            else {
               return result;
            }

            // ***** TypeBinding - class imports
         }
         else if (binding instanceof ITypeBinding) {
            if (currentTask.isMethod()) {
               continue;
            }
            IType type = null;
            try {
               type = compilationUnit.getJavaProject().findType(
                        ((ITypeBinding) binding).getQualifiedName());
               if (type == null || !type.getElementName().equals(resolveString)) {
                  continue;
               }

               ASTNode node = null;

               if (type.getClassFile() != null) {
                  node = JDTUtil.parse(type.getClassFile());
               }
               else if (type.getCompilationUnit() != null) {
                  node = JDTUtil.parse(type.getCompilationUnit());
               }

               return getTypeInCompilationUnit(resolveString, node);
            }
            catch (final JavaModelException e) {
               LogUtil.getLogger().logError(e);
               continue;
            }

            // Static Method Import
         }
         else if (binding instanceof IMethodBinding) {
            if (!currentTask.isMethod() || currentTask.isClass()) {
               continue;
            }
            IType type = null;
            try {
               type = compilationUnit.getJavaProject().findType(((IMethodBinding) binding).getDeclaringClass().getQualifiedName());

               final IMethodBinding mb = (IMethodBinding) binding;
               if (type == null || !mb.getName().equals(resolveString)) {
                  continue;
               }
               final LinkedList<MethodDeclaration> result = new LinkedList<MethodDeclaration>();
               final ASTVisitor methodFinder = new ASTVisitor() {

                  @Override
                  public boolean visit(final MethodDeclaration node) {
                     if (mb.getJavaElement().equals(node.resolveBinding().getJavaElement())) {
                        result.add(node);
                        return false;
                     }
                     return super.visit(node);
                  }
               };

               if (type.getClassFile() != null) {
                  JDTUtil.parse(type.getClassFile()).accept(methodFinder);
               }
               else if (type.getCompilationUnit() != null) {
                  JDTUtil.parse(type.getCompilationUnit()).accept(methodFinder);
               }
               if (!result.isEmpty()) {
                  return result.poll();
               }

            }
            catch (final JavaModelException e) {
               LogUtil.getLogger().logError(e);
               return null;
            }

            // Static Variable Imports
         }
         else if (binding instanceof IVariableBinding) {
            if (currentTask.isClass() || currentTask.isMethod()) {
               continue;
            }
            IType type = null;
            try {
               type = compilationUnit.getJavaProject().findType(
                        ((IVariableBinding) binding).getDeclaringClass().getQualifiedName());

               final IVariableBinding vb = (IVariableBinding) binding;
               if (type == null || !vb.getName().equals(resolveString)) {
                  continue;
               }
               final LinkedList<VariableDeclaration> result = new LinkedList<VariableDeclaration>();

               final ASTVisitor variableFinder = new ASTVisitor() {

                  @Override
                  public boolean visit(final VariableDeclarationFragment node) {
                     if (vb.getJavaElement().equals(node.resolveBinding().getJavaElement())) {
                        result.add(node);
                        return false;
                     }
                     return super.visit(node);
                  }
               };

               if (type.getClassFile() != null) {
                  JDTUtil.parse(type.getClassFile()).accept(variableFinder);
               }
               else if (type.getCompilationUnit() != null) {
                  JDTUtil.parse(type.getCompilationUnit()).accept(variableFinder);
               }

               if (!result.isEmpty()) {
                  return result.poll();
               }

            }
            catch (final JavaModelException e) {
               LogUtil.getLogger().logError(e);
               return null;
            }

         }
         else {
            throw new ResolverException("ImportDeclaration returned an unrecognised IBinding.", originalNode, null);
         }
      }

      return null;
   }

   /**
    * Searches for fields with the given name in the given context.
    * 
    * @param context is the context this method is searching in. Should be a
    *           {@link TypeDeclaration}, {@link FieldDeclaration} or
    *           {@link VariableDeclarationFragment}
    * @param name is the name of the identifier we are searching for
    * @return the {@link ASTNode} corresponding to the name in the given context
    */
   private ASTNode findField(final ASTNode context, final String name) {

      if (context == null || name == null) {
         return null;
      }
      
      final LinkedList<VariableDeclarationFragment> result = new LinkedList<VariableDeclarationFragment>();
      
      context.accept(new ASTVisitor() {  
         
         @Override
         public boolean visit(final TypeDeclaration node) {
            if(node.subtreeMatch(new ASTMatcher(), context)) {
               return true;
            }
            return false;
         }
         
         @Override
         public boolean visit(final ForStatement node) {
            return false;
         }
         
         @Override
         public boolean visit(final WhileStatement node) {
            return false;
         }
         
         @Override
         public boolean visit(final SwitchStatement node) {
            return false;
         }
         
         @Override
         public boolean visit(final MethodDeclaration node) {
            return false;
         }
         
         @Override
         public boolean visit(final VariableDeclarationFragment node) {
            if(result.size() > 0) {
               return false;
            }
            if(node.getName().getIdentifier().equals(name)) {
               result.add(node);
               return false;
            }
            return true;
         }
      });
      
      return result.poll();
   }

   /**
    * Searches for parameters with the given name in the given context.
    * 
    * @param context is the context this method is searching in. Should be a
    *           {@link MethodDeclaration}
    * @param name is the name of the identifier we are searching for
    * @return the {@link ASTNode} corresponding to the name in the given context
    */
   private ASTNode findParameters(final ASTNode context, final String name) {

      if (context == null || name == null) {
         return null;
      }

      if (context instanceof MethodDeclaration) {
         if (!((MethodDeclaration) context).isConstructor()) {
            for (final Object parameter : ((MethodDeclaration) context).parameters()) {
               final ASTNode result = findParameters((ASTNode) parameter, name);
               if (result != null) {
                  return result;
               }
            }
         }
         // SingleVariableDeclaration
      }
      else if (context instanceof SingleVariableDeclaration) {
         if (((SingleVariableDeclaration) context).getName().getIdentifier().equals(name)) {
            return context;
         }
      }
      return null;
   }

   /**
    * Resolves the binding of the given {@link ASTNode} if possible.
    * 
    * @param jdtNode - the {@link ASTNode} we try to resolve the binding for
    * @return the {@link IBinding} if it was possible to be resolved, null otherwise
    */
   private IBinding resolveBinding(final ASTNode jdtNode) {
      IBinding binding = null;

      if (jdtNode instanceof TypeDeclaration) {
         binding = ((TypeDeclaration) jdtNode).resolveBinding();
      }
      else if (jdtNode instanceof MethodDeclaration) {
         binding = ((MethodDeclaration) jdtNode).resolveBinding();
      }
      else if (jdtNode instanceof SingleVariableDeclaration) {
         binding = ((SingleVariableDeclaration) jdtNode).resolveBinding();
      }
      else if (jdtNode instanceof VariableDeclarationFragment) {
         binding = ((VariableDeclarationFragment) jdtNode).resolveBinding();
      }
      else if (jdtNode instanceof Type) {
         binding = ((Type) jdtNode).resolveBinding();
      }
      else if(jdtNode instanceof TypeParameter) {
         binding = ((TypeParameter)jdtNode).resolveBinding();
      }
      return binding;
   }

   /**
    * Get the {@link ResolveResultType} for the given {@link ASTNode}.
    * 
    * @param jdtNode - the {@link ASTNode}
    * @return a {@link ResolveResultType}. It has the value {@code UNSPECIFIED} if the type
    *         could not be found.
    */
   private ResolveResultType getResolveType(final ASTNode jdtNode) {
      ResolveResultType resultType = ResolveResultType.UNSPECIFIED;

      if (jdtNode instanceof TypeDeclaration || jdtNode instanceof TypeParameter) {
         resultType = ResolveResultType.CLASS;
      }
      else if (jdtNode instanceof MethodDeclaration) {
         resultType = ResolveResultType.METHOD;
      }
      else if (jdtNode instanceof SingleVariableDeclaration) {
         resultType = ResolveResultType.PARAMETER;
      }
      else if (jdtNode instanceof VariableDeclarationFragment) {
         resultType = ResolveResultType.FIELD;
      }
      return resultType;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public final boolean hasNext() {
      return tasks.size() > 0 ? true : false;
   }
}