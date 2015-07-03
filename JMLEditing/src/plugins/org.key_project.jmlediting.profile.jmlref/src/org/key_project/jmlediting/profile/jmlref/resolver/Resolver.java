package org.key_project.jmlediting.profile.jmlref.resolver;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
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
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.Type;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.eclipse.jdt.internal.core.JavaProject;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.DefaultTypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.typecomputer.JMLTypeComputer;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

/**
 * The Resolver class, that only has two public methods.
 * <br>"resolve({@link ICompilationUnit}, {@link IASTNode}) -> {@link ResolveResult}" that will resolve the 
 * {@link IASTNode} given and find the corresponding JavaElement or JML declaration and
 * <br>"next() -> {@link ResolveResult} that will resolve any member access that is appended to the 
 * original identifier.
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
    
    /**
     * {@inheritDoc}
     * @throws ResolverException 
     */
    @SuppressWarnings("unchecked")
    @Override
    public ResolveResult resolve(final ICompilationUnit compilationUnit, final IASTNode jmlNode) throws ResolverException {
                
        // check if the given IASTNode is correct and get possible information
        if(jmlNode == null || compilationUnit == null) {
            return null;
        }
        
        // reset everything .. so we can resolve more than one identifier, with one instance.
        context = null;
        this.compilationUnit = compilationUnit;
        commentToAST.clear();
        imports.clear();
        tasks.clear();
        currentTask = null;
        
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
     * @throws ResolverException 
     */
    @Override
    public ResolveResult next() throws ResolverException {
        currentTask = tasks.poll();
        // no more task?
        if(currentTask == null) {
            return null;
        }
        
        ASTNode jdtNode = null;
        if(!currentTask.isKeyword) {
            jdtNode = findIdentifier();
        } else {
            jdtNode = processKeyword();
        }
        
        if(currentTask.isArrayAcess) {
            // TODO: test if found jdtNode is an array... 
            // else .. resolve failed.
        }
        if(jdtNode == null) {
            return null;
        }
        final ResolveResult finalResult = new ResolveResult(jdtNode, getResolveType(jdtNode), resolveBinding(jdtNode));
        
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
     */
    private ASTNode findIdentifier() {
        ASTNode jdtNode = null;
        
        if(currentTask.lastResult != null) {
            // set new context
            context = JDTUtil.parse((ICompilationUnit) DefaultTypeComputer.getTypeFromBinding(currentTask.lastResult.getBinding()).getJavaElement());
        } else if(!currentTask.isMethod) {
            // If we get in here, this is the first call of this function, means our context is set to
            // the method/code the comment is bound to.
            jdtNode = findParameters(context, currentTask.resolveString);
        }
        
        if(jdtNode == null) {   
            // TODO: go up step by step ?
            context = context.getRoot();
            
            if(currentTask.isMethod) {
                jdtNode = findMethod(context, currentTask.resolveString);
            } else {
                jdtNode = findField(context, currentTask.resolveString);
            }
        }
        
        if(jdtNode == null) {
            jdtNode = findFromImports(currentTask.resolveString);
        }
        
        // return what we found... either null or the jdtNode
        return jdtNode;
    }
    
    private ASTNode findFromImports(final String resolveString) {
        // TODO: search in import list
        for(final ImportDeclaration imp : imports) {
            
            final IBinding binding = imp.resolveBinding();
            
            // TODO : IJavaProject.find...(...) um Imports zu finden
       
            
            if(binding instanceof IPackageBinding) {
                // TODO ?
                System.out.println("IPackageBinding");
                
            // ***** TypeBinding 
            } else if(binding instanceof ITypeBinding) {
                IType type = null;
                try {
                    type = compilationUnit.getJavaProject().findType(((ITypeBinding) binding).getQualifiedName());
                    if(type == null) {
                        return null;
                    }
                    if(type.getClassFile() != null) {
                        return JDTUtil.parse(type.getClassFile());
                    } else if(type.getCompilationUnit() != null) {
                        return JDTUtil.parse(type.getCompilationUnit());
                    }
                }
                catch (final JavaModelException e) {
                    LogUtil.getLogger().logError(e);
                    return null;
                }
                
            } else if(binding instanceof IMethodBinding) {
                IType type = null;
                try {
                    type = compilationUnit.getJavaProject().findType(((IMethodBinding) binding).getDeclaringClass().getQualifiedName());
                    if(type == null) {
                        return null;
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
                // TODO ?
                System.out.println("IVariableBinding");
                
            } else {
                
            }
            System.out.println(binding.getName());
            
            System.out.println(binding.getJavaElement());
            
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
    private ASTNode findMethod(final ASTNode context, final String name) {
               
        if(context == null || name == null) {
            return null;
        }
        
        if(context instanceof CompilationUnit) {
            for(final Object types : ((CompilationUnit) context).types()) {
                final ASTNode result = findMethod((ASTNode) types, name);
                if(result != null) {
                    return result;
                }
            }
        // TYPE DECLARATION
        } else if(context instanceof TypeDeclaration) {            
            for(final MethodDeclaration method : ((TypeDeclaration) context).getMethods()) {
                final ASTNode result = findMethod(method, name);
                if(result != null) {
                    return result;
                }
            }
            
        // METHOD DECLARATION
        } else if(context instanceof MethodDeclaration) {
            if(((MethodDeclaration) context).getName().getIdentifier().equals(name)) {
                // TODO: is this a declaration that matches?
                return checkMethodDeclaration((MethodDeclaration) context);
            }
        }
        return null;
    }

    /** Check the {@link MethodDeclaration} whether it matches the one we are searching for.
     * <br>This method assumes, that the names are already matching and only checks if the types of the parameters are of the same type.
     * It uses the {@link JMLTypeComputer} to compute the types of the parameters, since they can be very complicated.
     * 
     * @param context is the {@link MethodDeclaration} we are checking
     * @return the {@link ASTNode} given as context, if all the parameter types match, else it returns null
     */
    private ASTNode checkMethodDeclaration(final MethodDeclaration context) {
        
        // if the parameter count differs.. this method can not be the one we are searching for.
        if(currentTask.parameters.size() != context.parameters().size()) {
            return null;
        }
        
        // if there are no parameters, it must be the correct one.
        if(currentTask.parameters.size() == 0) {
            return context;
        }
        
        // we have to check the types of the parameters .. 
        for(int i = 0; i < currentTask.parameters.size() ; i++) {
            final JMLTypeComputer tc = new JMLTypeComputer(compilationUnit);
                        
            final ITypeBinding b1 = DefaultTypeComputer.getTypeFromBinding(resolveBinding((ASTNode) context.parameters().get(i)));
            ITypeBinding b2 = null;
            try {
                b2 = tc.computeType(currentTask.parameters.get(i));
            }
            catch (final TypeComputerException e) {
                // Parameter is not a valid type or has mismatches... 
                return null;
            }
            
            // if parameters are not matching or work together 
            // .. this is not the method we are looking for
            if(!DefaultTypeComputer.typeMatch(b1, b2)) {
                return null;
            }
        }
        return context;
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
     * @throws ResolverException is thrown, if the jmlNode isn't build correctly.
     */
    protected void buildResolverTask(final IASTNode jmlNode) throws ResolverException {
    
        try{
            if(isPrimaryExpr(jmlNode)) {
                
            } else if(isCast(jmlNode)) {
                // TODO:                
            } else {
                throw new ResolverException("Given IASTNode is not resolvable.");
            }
        } catch(final NullPointerException e) {
            throw new ResolverException("Given IASTNode is not resolvable. "
                    + "A NullPointerException occured while trying to access childs.", e);
        }
        
    }

    protected boolean isPrimaryExpr(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
            // PRIMARY
            System.out.print("[Primary]");
            
            tasks.add(new ResolverTask());

            result = isIdentifier(node.getChildren().get(0)) 
                  || isJmlPrimary(node.getChildren().get(0))
                  || isJavaKeyword(node.getChildren().get(0));
            
            if(node.getChildren().size() > 1) {
                System.out.println();
                
                result = isList(node.getChildren().get(1));
                
            } else {
                result = true;
            }
            
        }
        System.out.println();
        return result;
    }
    
    protected boolean isJavaKeyword(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.JAVA_KEYWORD) {
            
            tasks.getLast().isKeyword  = true;
            
            result = isString(node.getChildren().get(0));
        }
        return result;
    }
    
    protected boolean isJmlPrimary(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.JML_PRIMARY) {                    
            // PRIMARY -> JML_PRIMARY
            System.out.print("[JML Primary]");
            
            result = isKeyword(node.getChildren().get(0));
        }
        return result;
    }
    
    protected boolean isCast(final IASTNode node) {
        // TODO: Not sure yet.. if this should be here.
        boolean result = false;
        result = true;
        System.out.println("[Cast]");
        return result;
    }

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

    protected boolean isIdentifier(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.IDENTIFIER) {                    
            // PRIMARY -> IDENTIFIER
            
            System.out.print("[Identifier]");
                          
            result = isString(node.getChildren().get(0));
        }
        return result;
    }
    
    protected boolean isString(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.STRING) {
            // PRIMARY -> IDENTIFIER -> STRING
            System.out.print("[String]->"+((IStringNode)node).getString());
            
            // set resolveString! :)
            tasks.getLast().resolveString = ((IStringNode)node).getString();
            tasks.getLast().node = (IStringNode) node;
            
            result = true;
        }
        return result;
    }
    
    protected boolean isList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.LIST) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST
            System.out.print("[List]");
            
            for(final IASTNode child : node.getChildren()) {
                result = isMethodCall(child) || isMemberAccess(child) || isArrayAccess(child);
            }
        }
        return result;
    }
    
    protected boolean isArrayAccess(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.ARRAY_ACCESS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> ARRAY_ACCESS
            System.out.print("[ARRAYACCESS]");
            
            //tasks.getLast().type = ResolverTaskTypes.ARRAY_ACCESS;
            tasks.getLast().isArrayAcess = true;
            // TODO: test parameter ? if Int?
            
            result = true;
        }
        return result;
    }

    protected boolean isMethodCall(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL
            System.out.print("[Method Call]");
            
            //tasks.getLast().type = ResolverTaskTypes.METHOD_CALL;
            tasks.getLast().isMethod = true;
            
            result = isExpressionList(node.getChildren().get(0)) || isEmptyList(node.getChildren().get(0));
        }
        return result;
    }
    
    protected boolean isEmptyList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == NodeTypes.NONE) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL -> NONE
            System.out.print("[EXPRESSION_LIST]");
           
            result = true;
        }
        return result;
    }

    protected boolean isExpressionList(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.EXPRESSION_LIST) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> METHOD_CALL -> EXPRESSION_LIST
            System.out.print("[EXPRESSION_LIST]");
            
            for(final IASTNode child : node.getChildren()) {
                tasks.getLast().parameters.add(child);
                result = true;
            }
        }
        return result;
    }

    protected boolean isMemberAccess(final IASTNode node) {
        boolean result = false;
        if(node.getType() == ExpressionNodeTypes.MEMBER_ACCESS) {
            // PRIMARY -> IDENTIFIER -> STRING
            //         -> LIST       -> MEMBER_ACCESS
            tasks.add(new ResolverTask());
            //tasks.getLast().type = ResolverTaskTypes.MEMBER_ACCESS;
            tasks.getLast().node = (IStringNode) node.getChildren().get(1);
            tasks.getLast().resolveString = tasks.getLast().node.getString();
            
            System.out.print("[Member Access: "+node.getChildren().get(0)+node.getChildren().get(1)+"]");
                        
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
    
    /*private void debug() {
                
        
        // get all the imports from the given compilationUnit        
        
        IJavaElement element = compilationUnit;
        
        while(element != null) {
            if(element.getElementType() == IJavaElement.COMPILATION_UNIT) {
                System.out.print("ICompilationUnit: ");
                
            } else if(element.getElementType() == IJavaElement.PACKAGE_FRAGMENT) {
                System.out.print("IPackageFragment: ");
                try {
                    for(final IJavaElement child : ((IPackageFragment)element).getChildren()) {
                        javaElementList.add(child);
                    }
                }
                catch (final JavaModelException e) {
                    e.printStackTrace();
                }
                
                
            } else if(element.getElementType() == IJavaElement.PACKAGE_FRAGMENT_ROOT) {
                System.out.print("IPackageFragmentRoot: ");
                
            } else if(element.getElementType() == IJavaElement.JAVA_PROJECT) {
                System.out.print("IJavaProject: ");
                
            } else if(element.getElementType() == IJavaElement.JAVA_MODEL) {
                System.out.print("IJavaModel: ");
                
            }
            System.out.println(element.getElementName());
            element = element.getParent();
        }
        
        try {
            System.out.println("ICompilationUnits in all of this: ");
            int i = 0;
            for(final ICompilationUnit unit : JDTUtil.listCompilationUnit(javaElementList)) {
                System.out.println(i++ + " - " + unit.getElementName());
            }
        }
        catch (final JavaModelException e1) {
            e1.printStackTrace();
        }  
        
        
        try {
            for(final IImportDeclaration imp : compilationUnit.getImports()) {
                System.out.println(imp.getElementName());
            }
        }
        catch (final JavaModelException e1) {
            LogUtil.getLogger().logError(e1);
        }
        

        // ***************************************** This is for testing only.
        /*final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(compilationUnit);
        final AST ast = jdtAST.getAST();
        
        final ITypeBinding test = ast.resolveWellKnownType("java.lang.String");
        //test.getQualifiedName();
        IJavaElement element = test.getJavaElement();
        while(element != null && !(element.getElementType() == IJavaElement.COMPILATION_UNIT || element.getElementType() == IJavaElement.CLASS_FILE)) {
            element = element.getParent();
        }
        if(element != null && element.getElementType() == IJavaElement.COMPILATION_UNIT ) {
            final CompilationUnit jdtAST2 = (CompilationUnit) JDTUtil.parse((ICompilationUnit)element);
            jdtAST2.getAST();
        }
        if(element != null && element.getElementType() == IJavaElement.CLASS_FILE ) {
            final CompilationUnit jdtAST2 = (CompilationUnit) JDTUtil.parse((IClassFile)element);
            jdtAST2.getAST();
        }*/
                
        /*
         * ast.resolveWellKnownType(name);
         * 
         * "boolean"
        •"byte"
        •"char"
        •"double"
        •"float"
        •"int"
        •"long"
        •"short"
        •"void"
        •"java.lang.AssertionError" (since 3.7)
        •"java.lang.Boolean" (since 3.1)
        •"java.lang.Byte" (since 3.1)
        •"java.lang.Character" (since 3.1)
        •"java.lang.Class"
        •"java.lang.Cloneable"
        •"java.lang.Double" (since 3.1)
        •"java.lang.Error"
        •"java.lang.Exception"
        •"java.lang.Float" (since 3.1)
        •"java.lang.Integer" (since 3.1)
        •"java.lang.Long" (since 3.1)
        •"java.lang.Object"
        •"java.lang.RuntimeException"
        •"java.lang.Short" (since 3.1)
        •"java.lang.String"
        •"java.lang.StringBuffer"
        •"java.lang.Throwable"
        •"java.lang.Void" (since 3.1)
        •"java.io.Serializable"
         */
    //}
    
}
