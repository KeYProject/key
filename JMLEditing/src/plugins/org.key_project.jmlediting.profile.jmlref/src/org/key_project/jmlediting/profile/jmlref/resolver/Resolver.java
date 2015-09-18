package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.jar.Attributes.Name;

import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.QualifiedName;
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
 * The Resolver class, that only has three public methods.
 * <br>"{@code resolve}({@link ICompilationUnit}, {@link IASTNode}) -> {@link ResolveResult}" that will resolve the 
 * {@link IASTNode} given and find the corresponding JavaElement or JML declaration and
 * <br>"{@code next()} -> {@link ResolveResult}" that will resolve any member access that is appended to the 
 * original identifier.
 * <br>"{@code hasNext()} -> boolean" that will return true, if the taskList is not empty and there is still something to resolve with the next() method.
 * 
 * @author Christopher Beckmann
 */
public class Resolver implements IResolver {
    
    /** ResolverTask is a container for information, that will be used every time next() is called in the {@link Resolver} class.
     * 
     * @author Christopher Beckmann
     */
    private final class ResolverTask {
        public boolean isMethod = false;
        public boolean isArrayAcess = false;
        public boolean isKeyword = false;
        public String resolveString = null;
        public IStringNode node = null;
        public final List<IASTNode> parameters = new LinkedList<IASTNode>();
        public ResolveResult lastResult = null;
    }

    private ASTNode context = null;
    private ICompilationUnit compilationUnit = null;
    private final Map<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();
    private final List<ImportDeclaration> imports = new ArrayList<ImportDeclaration>();
    private final LinkedList<ResolverTask> tasks = new LinkedList<ResolverTask>();
    private ResolverTask currentTask = null;
    private PackageDeclaration pack = null;
    
    /**
     * {@inheritDoc}
     */
    @SuppressWarnings("unchecked")
    @Override
    public ResolveResult resolve(final ICompilationUnit compilationUnit, final IASTNode jmlNode) throws ResolverException {
                
        // check if the given IASTNode is correct and get possible information
        if(jmlNode == null || compilationUnit == null) {
            return null;
        }
        
        // reset everything .. so we can resolve more than once, with one instance or a resolver
        reset(compilationUnit);
        
        // First, we get all the information about, what we have to resolve by checking the given IASTNode.
        // this builds up the task list.
        buildResolverTask(jmlNode);
        
        // Parse JML and map nodes to JDT
        // Parse JDT first
        final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(compilationUnit);
        
        pack = jdtAST.getPackage();
        
        // Locate the comments
        String source = null;
        try {
            source = compilationUnit.getSource();
        } catch(final JavaModelException e) {
            LogUtil.getLogger().logError(e);
            return null;
        }
        
        // Finding the whole JML comment which contains our IASTNode by
        // getting all JDT comments (everything with // or /*)
        // and filtering those for comments which start with either //@ or /*@
        List<Comment> jdtcomments = jdtAST.getCommentList();
        
        final ArrayList<Comment> jmlcomments = new ArrayList<Comment>();
        
        Comment jmlComment = null;
        
        // Filtering the JDT comments
        for (Comment comment : jdtcomments){
            
            int commentStart = comment.getStartPosition();
            String stringToCompare = source.substring(commentStart, commentStart+3);
            
            if (stringToCompare.equals("//@") || stringToCompare.equals("/*@"))
            {
                jmlcomments.add(comment);
                
                // check if the JML comment contains our IASTNode that is supposed to be resolved
                if (commentStart <= jmlNode.getStartOffset() &&
                        commentStart + comment.getLength() >= jmlNode.getEndOffset())
                    jmlComment = comment;
            }
        }

        
        // this maps every jdt comment to the jdt ASTNode it belongs to.
        jdtAST.accept(new ASTVisitor() {
            
            @Override
            public boolean preVisit2(final ASTNode node) {
                // Check if the node has a comment at all
                final int start = jdtAST.firstLeadingCommentIndex(node);
                if (start != -1) {
                    // extended start = start if JML in between Javadoc and Node (e.g. method)
                    // extended start < start if JML above Javadoc.
                    // Note that it will not be extended if an empty line is between JML and Javadoc.
                    final int extStartNode = jdtAST.getExtendedStartPosition(node);
                    final int extEndNode = extStartNode + jdtAST.getExtendedLength(node);
                    
                    // JML belongs to the node if it is in between the extended area covered by the node
                        
                        if (commentStart >= extStartNode && commentEnd < extEndNode){
                          assert !commentToAST.containsKey(comment);
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
        
        for (Comment comment : jmlcomments){
            if (!commentToAST.containsKey(comment)){
                ASTNode compUnitType = getTypeInCompilationUnit(compilationUnit.getElementName().substring(0, compilationUnit.getElementName().lastIndexOf('.')), jdtAST);
                commentToAST.put(comment, compUnitType);
            }
        }
        
        // now we have all the information we need
        
        return next();
    }

    /** Reset everything to their default values.
     * @param compilationUnit the {@link ICompilationUnit} to reset to.
     */
    private void reset(final ICompilationUnit compilationUnit) {
        context = null;
        this.compilationUnit = compilationUnit;
        commentToAST.clear();
        imports.clear();
        tasks.clear();
        currentTask = null;
        pack = null;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public ResolveResult next() throws ResolverException {
        currentTask = tasks.poll();
        // no more task?
        if(currentTask == null) {
            return null;
        }
        
        ASTNode jdtNode = null;
        IBinding binding = null; 
        ResolveResultType resultType;    
        
        if(!currentTask.isArrayAcess) {
            
            if(currentTask.isKeyword) {
                jdtNode = processKeyword();
            } else {
                jdtNode = findIdentifier();
            }
            
            if(jdtNode == null) {
                return null;
            }
            
            binding = resolveBinding(jdtNode);
            resultType = getResolveType(jdtNode);
            
        } else {
            
            jdtNode = currentTask.lastResult.getJDTNode();
            binding = TypeComputer.getTypeFromBinding(currentTask.lastResult.getBinding()).getComponentType();
            resultType = ResolveResultType.ARRAY_ACCESS;
            
            if(binding == null) {
                throw new ResolverException("Tried to perform an array access on a non array.");
            }
            
        }
            
        final ResolveResult finalResult = new ResolveResult(jdtNode, resultType, binding);
        
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
                return findMethodReturnValue();
            }
        }
        return null;
    }

    private TypeDeclaration getDeclaringClass(final ASTNode context) {
        ASTNode clazz = context;
        while((clazz != null) && !(clazz instanceof TypeDeclaration) &&
                clazz.getParent() != null) {
            clazz = clazz.getParent();
        }
        return (TypeDeclaration)clazz;
    }

    private ASTNode findMethodReturnValue() throws ResolverException {
        if(context instanceof MethodDeclaration) {
            return ((MethodDeclaration) context).getReturnType2();
        } else {
            throw new ResolverException("Context is not set to a MethodDeclaration.");
        }
    }

    /**
     * Searches for the {@link ASTNode} specified by {@code currentTask}.
     * @return the {@link ASTNode} or null if it could not be found
     * @throws ResolverException is thrown if the setNewContext method throws a ResolverException
     */
    private ASTNode findIdentifier() throws ResolverException {
        ASTNode jdtNode = null;
        
        if(currentTask.lastResult != null) {
            // set new context
            context = setNewContext();
            
        } else if(!currentTask.isMethod) {
            // If we get in here, this is the first call of this function, means our context is set to
            // the method/code the comment is bound to.
            jdtNode = findParameters(context, currentTask.resolveString);
        }
        
        // we need to get more information, in particular which class declared the method/field.
        if(jdtNode == null && currentTask.lastResult == null) {
            context = getDeclaringClass(context);
        }
        
        if(jdtNode == null) {
            if(currentTask.isMethod) {
                // TODO: WHY?
                context = getDeclaringClass(context);

                final IType type = (IType) ((TypeDeclaration)context).resolveBinding().getJavaElement();
                
                /*for(IMethodBinding methodBinding : ((TypeDeclaration)context).resolveBinding().getDeclaredMethods()) {
                    methodBinding.
                }*/
                
                
                //System.out.println(type.getFullyQualifiedName());
                final IMethod method = type.getMethod(currentTask.resolveString, createParameterSignatures(currentTask.parameters));
                try {
                    final IMethod[] allMethods = type.getMethods();
                    
                }
                catch (final JavaModelException e) {
                    LogUtil.getLogger().logError(e);
                }
                //TODO .. problem still exists with parameterized types
                //type.findMethods(method);
                
                return findIMethod(context, method);
                
                
                //final List<ASTNode> resultList = new LinkedList<ASTNode>();
                //findMethod(context, currentTask.resolveString, resultList);
                //if(resultList.size() > 0) {
                    // pick the best one... change list to a hashmap maybe?
                //    jdtNode = resultList.get(0);
                //}
            } else {
                jdtNode = findField(context, currentTask.resolveString);
            }
        }
        
        if(jdtNode == null) {
            jdtNode = findInPackage(currentTask.resolveString, pack.resolveBinding());
        }
        if(jdtNode == null) {
            jdtNode = findFromImports(currentTask.resolveString);
        }
        
       if (jdtNode == null) {
            jdtNode = findNextReferencesClass(currentTask.resolveString);
        }
        
        // return what we found... either null or the jdtNode
        return jdtNode;
    }


    private ASTNode findNextReferencesClass(final String resolveString) {
        
        IJavaProject javaProject = compilationUnit.getJavaProject();
        
        LinkedList<ResolverTask> tasksToWorkWith = new LinkedList<ResolverTask>();
        tasksToWorkWith.addAll(tasks);
        
        final LinkedList<IType> result = new LinkedList<IType>();
        final SearchEngine se = new SearchEngine();
        
        String packToSearch = resolveString;
        String classToSearch = "";
        int tasksToRemove = 0;
        
        while (tasksToWorkWith.size() > 0 && result.size() == 0){
            
            classToSearch = tasksToWorkWith.removeFirst().resolveString;
            
            try {
                se.searchAllTypeNames(packToSearch.toCharArray(), SearchPattern.R_EXACT_MATCH, 
                        classToSearch.toCharArray(), SearchPattern.R_EXACT_MATCH,
                        IJavaSearchConstants.CLASS,
                        SearchEngine.createJavaSearchScope(new IJavaElement[] {javaProject}), 
                        new TypeNameMatchRequestor() {
                            @Override
                            public void acceptTypeNameMatch(final TypeNameMatch match) {
                                result.add(match.getType());
                            }
                        },
                        IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH, new NullProgressMonitor());
            }
            catch (JavaModelException e) {
                return null;
            }
            
            packToSearch = packToSearch + "." + classToSearch;
            tasksToRemove++;
        }
        
        if (result.size() > 0){
            IJavaElement foundClass = result.get(0).getParent();
            if (foundClass instanceof ICompilationUnit) {
                ICompilationUnit compUnitFound = (ICompilationUnit) foundClass;
                
                for (int i = tasksToRemove; i > 0; i--){
                    if (i == 1){
                        ResolverTask taskFoundClass = tasks.removeFirst();
                        currentTask = taskFoundClass;
                    } else {
                        tasks.removeFirst();
                    }
                }
                return (CompilationUnit) JDTUtil.parse(compUnitFound);
            }
        }
        
        return null;
    }

    private ASTNode findIMethod(final ASTNode context, final IMethod method) {
        final LinkedList<MethodDeclaration> result = new LinkedList<MethodDeclaration>();
        
        //final String key = method.getKey();
        
        final String[] expectedParameterKeys = Signature.getParameterTypes(method.getKey());
        //final String subkey2 = key.substring(key.indexOf("(")+1, key.indexOf(")"));
        
                
        context.accept(new ASTVisitor() {
            
            @Override
            public boolean visit(final MethodDeclaration node) {
                if(node.getName().getIdentifier().equals(method.getElementName())) {
                    final String[] actualParameterKeys = Signature.getParameterTypes(node.resolveBinding().getKey());
                    //final String key = node.resolveBinding().getKey();
                    //final String subkey = key.substring(key.indexOf("(")+1, key.indexOf(")"));
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
            // method was not defined in this class.
            final Type newContext = getDeclaringClass(context).getSuperclassType();
            try {
                if(newContext == null) {
                    // TODO:
                }
                
                final IType type = compilationUnit.getJavaProject().findType(newContext.resolveBinding().getQualifiedName());
                if(type == null) {
                    return null;
                }
                
                ASTNode node = null;
                if(type.getClassFile() != null) {
                    node = JDTUtil.parse(type.getClassFile());
                } else if(type.getCompilationUnit() != null) {
                     node = JDTUtil.parse(type.getCompilationUnit());
                }
                
                return findIMethod(node, method);
                
            }
            catch (final JavaModelException e) {
                LogUtil.getLogger().logError(e);
            }
        }
        
        return result.poll();
    }

    /** Uses the TypeComputer to find out what the ITypeBinding of the parameters are then creates the Signature of those Bindings.
     * 
     * @param parameters the List of the parameters
     * @return a String array containing the signatures of the parameter types in the same order.
     * @throws ResolverException if the TypeComputer can not compute the parameter type.
     */
    private String[] createParameterSignatures(final List<IASTNode> parameters) throws ResolverException {
        if(parameters.size() == 0) {
            return new String[0];
        }
        
       final String[] result = new String[currentTask.parameters.size()];
        
        for(int i = 0; i < currentTask.parameters.size(); i++) {
            final JMLTypeComputer tc = new JMLTypeComputer(compilationUnit);
            
            ITypeBinding b = null;
            try {
                b = tc.computeType(currentTask.parameters.get(i));
            }
            catch (final TypeComputerException e) {
                throw new ResolverException("TypeComputer threw an exception when trying to resolve a method parameter.", e);
            }
            if(b != null) {
                result[i] = Signature.createTypeSignature(b.getQualifiedName(), true);
            }
        }
        
        return result;
    }

    /** Uses the {@link SearchEngine} to get the class specified by resolveString.
     * @param resolveString the class name you are searching for
     * @param binding the {@link IPackageBinding} of the package that is used as a context to search in
     * @return the {@link ASTNode} of the {@link TypeDeclaration} of the class we are searching for
     */
    private ASTNode findInPackage(final String resolveString, final IPackageBinding binding) {
        // there might be a more efficient way of doing this.
        // on demand packages will be searched like this.
        final SearchEngine se = new SearchEngine();
        final LinkedList<IType> result = new LinkedList<IType>();
        
        try {
            se.searchAllTypeNames(pack.getName().getFullyQualifiedName().toCharArray(), 
                    SearchPattern.R_EXACT_MATCH, 
                    resolveString.toCharArray(), 
                    SearchPattern.R_EXACT_MATCH, 
                    IJavaSearchConstants.TYPE, 
                    SearchEngine.createJavaSearchScope(new IJavaElement[] {binding.getJavaElement()}), 
                    new TypeNameMatchRequestor() {
                        @Override
                        public void acceptTypeNameMatch(final TypeNameMatch match) {
                            result.add(match.getType());
                        }
                    },
                    IJavaSearchConstants.WAIT_UNTIL_READY_TO_SEARCH,
                    null);
        }
        catch (final JavaModelException e) {
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

    private ASTNode getTypeInCompilationUnit(final String resolveString, final ASTNode node) {
        final LinkedList<ASTNode> endResult = new LinkedList<ASTNode>();
        
        if(node != null && resolveString != null) {
            node.accept(new ASTVisitor() {
                @Override
                public boolean visit(final TypeDeclaration node) {
                    if(node.getName().getIdentifier() != null && node.getName().getIdentifier().equals(resolveString)) {
                        endResult.add(node);
                        return false;
                    }
                    return true;
                }
            });
        }
        return endResult.poll();
    }

    private ASTNode setNewContext() throws ResolverException {
        final ITypeBinding typeBinding = TypeComputer.getTypeFromBinding(currentTask.lastResult.getBinding());
        // START testing what the new context might be
        if(typeBinding.isPrimitive()) {
            throw new ResolverException("Can not resolve an access to a primitive type.");
        } else if(typeBinding.isArray()) {
            
            // TODO: We found an array .. what to do? What is the context we set to.          
            // Set context to Object for everything that isnt ".length" or ".clone()" 
            //      context.getAST().resolveWellKnownType("java.lang.Object");
            
        } else if(typeBinding.isParameterizedType()) {
            ITypeBinding[] parameterTypes = null;
            final ITypeBinding newTypeBinding = typeBinding.getErasure();
                
            // TODO: Save Parameters here.. 
            parameterTypes = typeBinding.getTypeArguments();
            
            //System.out.println(typeBinding.getQualifiedName());
            //System.out.println(newTypeBinding.getQualifiedName());
            return findASTNodeFromType(newTypeBinding);
        } else {
            //System.out.println(typeBinding.getQualifiedName());
            return findASTNodeFromType(typeBinding);
        }
        return null;
    }
    
    private ASTNode findASTNodeFromType(final ITypeBinding binding) {
        final IType type;
        try {
            type = compilationUnit.getJavaProject().findType(binding.getQualifiedName());
        }
        catch (final JavaModelException e) {
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
    
    private ASTNode findFromImports(final String resolveString) throws ResolverException {
        
        for(final ImportDeclaration imp : imports) {
            
            final org.eclipse.jdt.core.dom.Name n = imp.getName();
            /*        // Create an additional Import for java.lang.*
            final ImportDeclaration javaLang = jdtAST.getAST().newImportDeclaration();
            javaLang.setName(jdtAST.getAST().newQualifiedName(jdtAST.getAST().newSimpleName("java"), jdtAST.getAST().newSimpleName("lang")));
            javaLang.setOnDemand(true);
            javaLang.*/
            
            final IBinding binding = imp.resolveBinding();       
            // TODO: java.lang. package import
            if(binding instanceof IPackageBinding) {
                final ASTNode result = findInPackage(resolveString, (IPackageBinding) binding);
                if(result == null) {
                    continue;
                } else {
                    return result;
                }
                
            // ***** TypeBinding 
            } else if(binding instanceof ITypeBinding) {
                
                IType type = null;
                try {
                    type = compilationUnit.getJavaProject().findType(((ITypeBinding) binding).getQualifiedName());
                    if(type == null || !type.getElementName().equals(resolveString)) {
                        continue;
                    }
                    if(type.getClassFile() != null) {
                        return JDTUtil.parse(type.getClassFile());
                    } else if(type.getCompilationUnit() != null) {
                        return JDTUtil.parse(type.getCompilationUnit());
                    }
                }
                catch (final JavaModelException e) {
                    LogUtil.getLogger().logError(e);
                    continue;
                }
                
            } else if(binding instanceof IMethodBinding) {
                IType type = null;
                try {
                    type = compilationUnit.getJavaProject().findType(((IMethodBinding) binding).getDeclaringClass().getQualifiedName());
                    if(type == null) {
                        continue;
                    }
                    final IMethodBinding mb = (IMethodBinding) binding;
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
                        return result.poll();
                    } else if(type.getCompilationUnit() != null) {
                        JDTUtil.parse(type.getCompilationUnit()).accept(methodFinder);
                        return result.poll();
                    }
                }
                catch (final JavaModelException e) {
                    LogUtil.getLogger().logError(e);
                    return null;
                }
                
                
            } else if(binding instanceof IVariableBinding) {
                // TODO not implemented
                
            } else {
                throw new ResolverException("ImportDeclaration returned an unrecognised IBinding.");
            }
        }
        
        return null;
    }

    /**
     * Searches for fields with the given name in the given context.
     * @param context is the context this method is searching in. Should be a {@link CompilationUnit}, {@link TypeDeclaration}, {@link FieldDeclaration} or {@link VariableDeclarationFragment}
     * @param name is the name of the identifier we are searching for
     * @return the {@link ASTNode} corresponding to the name in the given context
     */
    private ASTNode findField(final ASTNode context, final String name) {

        if(context == null || name == null) {
            return null;
        }
        
        if(context instanceof CompilationUnit) {
            for(final Object types : ((CompilationUnit) context).types()) {
                final ASTNode result = findField((ASTNode) types, name);
                if(result != null) {
                    return result;
                }
            }
        // TYPE DECLERATION
        } else if(context instanceof TypeDeclaration) {
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
            
        //VariableDeclarationFragment
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
     * @param context is the context this method is searching in. Should be a {@link MethodDeclaration}
     * @param name is the name of the identifier we are searching for
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
        //SingleVariableDeclaration
        } else if(context instanceof SingleVariableDeclaration) {
            if(((SingleVariableDeclaration) context).getName().getIdentifier().equals(name)) {
                return context;
            }
        }
        return null;
    }
    
    /**
     * Resolves the binding of the given {@link ASTNode} if possible.
     * @param jdtNode - the {@link ASTNode} we try to resolve the binding for
     * @return the {@link IBinding} if it was possible to be resolved, null otherwise
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
     * @param jdtNode - the {@link ASTNode}
     * @return a {@link ResolveResultType}. It has the value 
     * {@code UNSPECIFIED} if the type could not be found.
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
     * @param jmlNode - the {@link IASTNode} that is supposed to be resolved.
     * @throws ResolverException is thrown, if the jmlNode isn't built correctly.
     */
    protected final void buildResolverTask(final IASTNode jmlNode) throws ResolverException {
        
        tasks.add(new ResolverTask());
        
        try{
            // This calls all the functions that build the resolver task list.
            // it's either a String (as in some assignable clauses or when the typeComputer
            // calls the resolver to resolve a type name) or it is a primary expression,
            // when called from a normal source that tries to resolve fields or methods. 
            final boolean result = isString(jmlNode) || isPrimaryExpr(jmlNode);
            if(result == false) {
                throw new ResolverException("Given IASTNode is not resolvable.");
            }
        
        } catch(final NullPointerException e) {
            throw new ResolverException("Given IASTNode is not resolvable. "
                    + "A NullPointerException occured while trying to access children.", e);
        }
        
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code PRIMARY_EXPR}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isPrimaryExpr(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
            // PRIMARY
            if(!isPrimaryExpr(node.getChildren().get(0))) {
                // Primaries may be cascaded.
                result = isIdentifier(node.getChildren().get(0)) 
                      || isJmlPrimary(node.getChildren().get(0))
                      || isJavaKeyword(node.getChildren().get(0));
            }
            // Process the Children of the Node
            if(node.getChildren().size() > 1) {
                result = isList(node.getChildren().get(1));
            }
        }
        return result;
    }
    
    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code JAVA_KEYWORD}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isJavaKeyword(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.JAVA_KEYWORD) {
            tasks.getLast().isKeyword  = true;
            result = isString(node.getChildren().get(0));
        }
        return result;
    }
    
    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code JML_PRIMARY}
     * @param node - the {@link IASTNode} to get information from
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
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link NodeTypes}.{@code KEYWORD}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isKeyword(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.KEYWORD && ((IKeywordNode)node).getKeywordInstance().equals("\\result")) {
            // PRIMARY -> JML_PRIMARY -> []
            tasks.getLast().isKeyword  = true;
            tasks.getLast().resolveString = ((IKeywordNode)node).getKeywordInstance();
            
            result = true;
        }
        return result;
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code IDENTIFIER}
     * @param node - the {@link IASTNode} to get information from
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
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link NodeTypes}.{@code STRING}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isString(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.STRING) {
            // PRIMARY -> IDENTIFIER -> STRING
            tasks.getLast().resolveString = ((IStringNode)node).getString();
            tasks.getLast().node = (IStringNode) node;
            result = true;
        }
        return result;
    }
    
    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link NodeTypes}.{@code LIST}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.LIST) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST            
            for(final IASTNode child : node.getChildren()) {
                result = isMethodCall(child) || isMemberAccess(child) || isArrayAccess(child);
            }
        }
        return result;
    }
    
    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code ARRAY_ACCESS}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isArrayAccess(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.ARRAY_ACCESS) {
            // PRIMARY -> []
            //         -> LIST       -> ARRAY_ACCESS
            tasks.add(new ResolverTask());
            tasks.getLast().isArrayAcess = true;
            
            result = true;
        }
        return result;
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code METHOD_CALL_PARAMETERS}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isMethodCall(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL
            tasks.getLast().isMethod = true;
            
            result = isExpressionList(node.getChildren().get(0)) || isEmptyList(node.getChildren().get(0));
        }
        return result;
    }
    
    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link NodeTypes}.{@code NONE}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isEmptyList(final IASTNode node) {
        // PRIMARY -> IDENTIFIER -> STRING
        //         -> LIST       -> METHOD_CALL -> NONE           
        return node.getType() == NodeTypes.NONE;
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code EXPRESSION_LIST}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isExpressionList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.EXPRESSION_LIST) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL -> EXPRESSION_LIST
            for(final IASTNode child : node.getChildren()) {
                tasks.getLast().parameters.add(child);
                result = true;
            }
        }
        return result;
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code MEMBER_ACCESS}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected final boolean isMemberAccess(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.MEMBER_ACCESS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> MEMBER_ACCESS
            tasks.add(new ResolverTask());
            tasks.getLast().node = (IStringNode) node.getChildren().get(1);
            tasks.getLast().resolveString = tasks.getLast().node.getString();
            result = true;
        }
        
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public final boolean hasNext() {
        if(tasks.size() > 0) {
            return true;
        }
        return false;
    }
}
