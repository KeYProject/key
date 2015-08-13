package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeParameter;
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
import org.eclipse.jdt.core.dom.MethodInvocation;
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
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
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
        context = null;
        this.compilationUnit = compilationUnit;
        commentToAST.clear();
        imports.clear();
        tasks.clear();
        currentTask = null;
        pack = null;
        
        // First, we get all the information about, what we have to resolve by checking the given IASTNode.
        // this builds up the task list.
        try{
            buildResolverTask(jmlNode);
        } catch(final ResolverException e) {
            LogUtil.getLogger().logError(e);
            return null;
        }
        
        // Parse JML and map nodes to JDT        
        // Parse JDT first
        final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(compilationUnit);
        
        imports.addAll(jdtAST.imports());
        pack = jdtAST.getPackage();
        
        // Get all the JDT comments so we can find the correct one.
        final List<Comment> jdtCommentList = jdtAST.getCommentList();
        
        // Locate the comments
        String source = null;
        try {
            source = compilationUnit.getSource();
        } catch(final JavaModelException e) {
            LogUtil.getLogger().logError(e);
            return null;
        }
        
        Comment jdtComment = null;
        
        final CommentLocator locator = new CommentLocator(source);
        
        for (final CommentRange jmlCommentRange : locator.findJMLCommentRanges()) {
            
            // Search for the correct CommentRange containing our IASTNode that is supposed to be resolved.
            if(jmlCommentRange.getBeginOffset() < jmlNode.getStartOffset() && jmlCommentRange.getEndOffset() >= jmlNode.getEndOffset()) {
                // Map the JML comment to the corresponding JDT comment.
                for (final Comment comment : jdtCommentList) {
                    // check if we got the correct JDT comment
                    if (jmlCommentRange.getBeginOffset() == comment.getStartPosition()) {
                        jdtComment = comment;
                        break;
                    }
                }
                // Go out of the for loop, because we found the correct jdt comment.
                break;
            }
        }
        
        // this maps every jdt comment to the jdt ASTNode it belongs to.
        jdtAST.accept(new ASTVisitor() {
            
            @Override
            public boolean preVisit2(final ASTNode node) {
                final int start = jdtAST.firstLeadingCommentIndex(node);
                if (start != -1) {
                    int pos = start;
                    while (pos < jdtCommentList.size()
                            && jdtCommentList.get(pos).getStartPosition() < node.getStartPosition()) {
                        final Comment comment = jdtCommentList.get(pos);
                        assert !commentToAST.containsKey(comment);
                        if(node.getNodeType() == ASTNode.PRIMITIVE_TYPE || node.getNodeType() == ASTNode.SIMPLE_TYPE) {
                            commentToAST.put(comment, node.getParent());
                        } else {
                            commentToAST.put(comment, node);
                        }
                        pos++;
                    }
                }
                return super.preVisit2(node);
            }
        });
        
        // now we have all the information we need
        context = commentToAST.get(jdtComment);
        
        return next();
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
                return getDeclaringClass();
            } else if(currentTask.resolveString.equals("super")) {
                return getDeclaringClass().getSuperclassType();
            } else if(currentTask.resolveString.equals("\\result")) {
                return findMethodReturnValue();
            }
        }
        return null;
    }

    private TypeDeclaration getDeclaringClass() {
        ASTNode clazz = context;
        while(!(clazz instanceof TypeDeclaration)) {
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
        
        if(jdtNode == null && currentTask.lastResult == null) {
            context = getDeclaringClass();
        }
        
        if(jdtNode == null) {
            if(currentTask.isMethod) {
                context = getDeclaringClass();
                
                final IType type = (IType) ((TypeDeclaration)context).resolveBinding().getJavaElement();
                
                //System.out.println(type.getFullyQualifiedName());
                final IMethod method = type.getMethod(currentTask.resolveString, createParameterSignatures(currentTask.parameters));
                
                //TODO .. problem still exists
                type.findMethods(method);
                
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
        
        // return what we found... either null or the jdtNode
        return jdtNode;
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
            result[i] = Signature.createTypeSignature(b.getQualifiedName(), true);
        }
        
        return result;
    }

    /**
     * Uses the {@link SearchEngine} to get the class specified by resolveString
     * @param resolveString the class name you are searching for
     * @param binding the {@link IPackageBinding} of the package that is used as a context to search in
     * @return the {@link ASTNode} of the {@link TypeDeclaration} of the class we are searching for
     */
    private ASTNode findInPackage(final String resolveString, final IPackageBinding binding) {
        // TODO: maybe more efficient way of doing this.
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
            throw new ResolverException("Can not resolve an access to a primite type.");
        } else if(typeBinding.isArray()) {
            // TODO: We found an array .. what to do? What is the context we set to?
        } else {
            IType type = null;
            try {
                if(typeBinding.isParameterizedType()) {
                    final ITypeBinding newTypeBinding = typeBinding.getErasure();
                    System.out.println(newTypeBinding.getQualifiedName());
                    type = compilationUnit.getJavaProject().findType(newTypeBinding.getQualifiedName());
                } else if(typeBinding.isWildcardType()) {
                    final ITypeBinding newTypeBinding = typeBinding.getGenericTypeOfWildcardType();
                    System.out.println(newTypeBinding.getQualifiedName());
                    type = compilationUnit.getJavaProject().findType(newTypeBinding.getQualifiedName());
                } else {
                    System.out.println(typeBinding.getQualifiedName());
                    type = compilationUnit.getJavaProject().findType(typeBinding.getQualifiedName());
                }
            }
            catch (final JavaModelException e) {
                LogUtil.getLogger().logError(e);
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
        return null;
    }
    
    private ASTNode findFromImports(final String resolveString) throws ResolverException {
        
        for(final ImportDeclaration imp : imports) {
            
            final IBinding binding = imp.resolveBinding();       
            
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
                // TODO 
                
            } else {
                throw new ResolverException("ImportDeclaration returned an unrecognised IBinding.");
            }
            //System.out.println(binding.getName());
            //System.out.println(binding.getJavaElement());
            
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
     * Searches for methods with the given name in the given context.
     * @param context is the context this method is searching in. Should be a {@link CompilationUnit}, {@link TypeDeclaration} or {@link MethodDeclaration}  
     * @param name is the name of the identifier we are searching for
     * @return the {@link ASTNode} corresponding to the name in the given context
     */
    /*private void findMethod(final ASTNode context, final String name, final List<ASTNode> resultList) {
        
        if(context == null || name == null) {
            return;
        }
        
        if(context instanceof CompilationUnit) {
            for(final Object types : ((CompilationUnit) context).types()) {
                findMethod((ASTNode) types, name, resultList);
            }
        // TYPE DECLARATION
        } else if(context instanceof TypeDeclaration) {            
            for(final MethodDeclaration method : ((TypeDeclaration) context).getMethods()) {
                findMethod(method, name, resultList);
            }
            
        // METHOD DECLARATION
        } else if(context instanceof MethodDeclaration) {
            if(((MethodDeclaration) context).getName().getIdentifier().equals(name)) {
                checkMethodDeclaration((MethodDeclaration) context, resultList);
            }
        }
        return;
    }*/

    /** Check the {@link MethodDeclaration} whether it matches the one we are searching for.
     * <br>This method assumes, that the names are already matching and only checks if the types of the parameters are of the same type.
     * It uses the {@link JMLTypeComputer} to compute the types of the parameters, since they can be very complicated.
     * 
     * @param context is the {@link MethodDeclaration} we are checking
     * @param resultList the list we add our result to, if it matches the specification
     * @return the {@link ASTNode} given as context, if all the parameter types match, else it returns null
     */
    /*private void checkMethodDeclaration(final MethodDeclaration context, final List<ASTNode> resultList) {
        
        // if the parameter count differs.. this method can not be the one we are searching for.
        if(currentTask.parameters.size() != context.parameters().size()) {
            return;
        }
        
        // if there are no parameters, it must be the correct one.
        if(currentTask.parameters.size() == 0) {
            resultList.add(context);
            return;
        }
        
        // we have to check the types of the parameters .. 
        for(int i = 0; i < currentTask.parameters.size() ; i++) {
            final JMLTypeComputer tc = new JMLTypeComputer(compilationUnit);
                        
            final ITypeBinding b1 = TypeComputer.getTypeFromBinding(resolveBinding((ASTNode) context.parameters().get(i)));
            ITypeBinding b2 = null;
            try {
                b2 = tc.computeType(currentTask.parameters.get(i));
            }
            catch (final TypeComputerException e) {
                // Parameter is not a valid type or has mismatches... 
                return;
            }
            
            // if parameters are not matching or work together 
            // .. this is not the method we are looking for
            if(!TypeComputer.typeMatch(b1, b2)) {
                return;
            }
        }
        resultList.add(context);
        return;
    }*/
    
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
     * @throws ResolverException is thrown, if the jmlNode isn't build correctly.
     */
    protected void buildResolverTask(final IASTNode jmlNode) throws ResolverException {
        
        tasks.add(new ResolverTask());
        
        try{
            if(isString(jmlNode)) {
                // for labels in assignable clause
            } else if(isPrimaryExpr(jmlNode)) {
                // for any expression in an ensures and so on
                //} else if(isCast(jmlNode)) {
                // expression that is cast to another type
            } else {
                throw new ResolverException("Given IASTNode is not resolvable.");
            }
        } catch(final NullPointerException e) {
            throw new ResolverException("Given IASTNode is not resolvable. "
                    + "A NullPointerException occured while trying to access childs.", e);
        }
        
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code PRIMARY_EXPR}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected boolean isPrimaryExpr(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
            // PRIMARY
            //System.out.print("[Primary]");

            result = isIdentifier(node.getChildren().get(0)) 
                  || isJmlPrimary(node.getChildren().get(0))
                  || isJavaKeyword(node.getChildren().get(0));
            
            if(node.getChildren().size() > 1) {
                //System.out.println();
                
                result = isList(node.getChildren().get(1));
                
            }
        }
        //System.out.println();
        return result;
    }
    
    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code JAVA_KEYWORD}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected boolean isJavaKeyword(final IASTNode node) {
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
    protected boolean isJmlPrimary(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.JML_PRIMARY) {                    
            // PRIMARY -> JML_PRIMARY
            //System.out.print("[JML Primary]");
            
            result = isKeyword(node.getChildren().get(0));
        }
        return result;
    }
    
    /*protected boolean isCast(final IASTNode node) {
        // Not sure yet.. if this should be here.
        boolean result = false;
        result = true;
        //System.out.println("[Cast]");
        return result;
    }*/

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link NodeTypes}.{@code KEYWORD}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected boolean isKeyword(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.KEYWORD && ((IKeywordNode)node).getKeywordInstance().equals("\\result")) {                    
            // PRIMARY -> JML_PRIMARY -> []
            //System.out.print("[Keyword]->"+((IKeywordNode)node).getKeywordInstance());   
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
    protected boolean isIdentifier(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.IDENTIFIER) {                    
            // PRIMARY -> IDENTIFIER
            
            //System.out.print("[Identifier]");
                          
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
    protected boolean isString(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.STRING) {
            // PRIMARY -> IDENTIFIER -> STRING
            //System.out.print("[String]->"+((IStringNode)node).getString());
            
            // set resolveString! :)
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
    protected boolean isList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.LIST) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST
            //System.out.print("[List]");
            
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
    protected boolean isArrayAccess(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.ARRAY_ACCESS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> ARRAY_ACCESS
            //System.out.print("[ARRAYACCESS]");
            
            tasks.add(new ResolverTask());
            
            //tasks.getLast().type = ResolverTaskTypes.ARRAY_ACCESS;
            tasks.getLast().isArrayAcess = true;
            // TODO: test parameter ? if Int?
            
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
    protected boolean isMethodCall(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL
            //System.out.print("[Method Call]");
            
            //tasks.getLast().type = ResolverTaskTypes.METHOD_CALL;
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
    protected boolean isEmptyList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.NONE) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL -> NONE
            //System.out.print("[NONE]");
           
            result = true;
        }
        return result;
    }

    /**
     * This method is part of the ResolverTask building process. It should be called on an {@link IASTNode} 
     * that has the type {@link ExpressionNodeTypes}.{@code EXPRESSION_LIST}
     * @param node - the {@link IASTNode} to get information from
     * @return true, if the node and every child node is correct.
     */
    protected boolean isExpressionList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.EXPRESSION_LIST) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL -> EXPRESSION_LIST
            //System.out.print("[EXPRESSION_LIST]");
            
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
    protected boolean isMemberAccess(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.MEMBER_ACCESS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> MEMBER_ACCESS
            tasks.add(new ResolverTask());
            //tasks.getLast().type = ResolverTaskTypes.MEMBER_ACCESS;
            tasks.getLast().node = (IStringNode) node.getChildren().get(1);
            tasks.getLast().resolveString = tasks.getLast().node.getString();
            
            //System.out.print("[Member Access: "+node.getChildren().get(0)+node.getChildren().get(1)+"]");
                        
            result = true;
        }
        
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean hasNext() {
        if(tasks.size() > 0) {
            return true;
        }
        return false;
    }
}
