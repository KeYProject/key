package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.eclipse.jdt.core.dom.FieldDeclaration;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

/**
 * The Resolver class, that only has a static method "resolve" that will resolve the {@link IASTNode} given and find the corresponding JavaElement or JML decleration.
 * 
 * 
 * @author Christopher Beckmann
 * 
 */
public class Resolver implements IResolver {
    
    private Comment jdtComment = null;
    private IASTNode jmlComment = null;
    private IASTNode identifier;
    private ASTNode jdtNode = null;
    private ASTNode originalContext = null;
    private String resolveString = null;
    private ICompilationUnit compilationUnit = null;
    private final Map<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();
    
    
    /**
     * {@inheritDoc}
     */
    @Override
    public ResolveResult resolve(final ICompilationUnit compilationUnit, final IASTNode identifier) {
        
        // check if the given IASTNode is correct and get possible information
        if(identifier == null || compilationUnit == null || identifier.getType() != NodeTypes.STRING) {
            return null;
        }

        this.compilationUnit = compilationUnit;
        this.identifier = identifier;
        resolveString = getString(identifier);
        
        // Parse JML and map nodes to JDT        
        // Parse JDT first
        final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(compilationUnit);
        
        // Get all the JDT comments so we can find the correct one.
        @SuppressWarnings("unchecked")
        final List<Comment> jdtCommentList = jdtAST.getCommentList();
        
        // Locate the comments
        String source = null;
        try {
            source = compilationUnit.getSource();
        } catch(final JavaModelException e) {
            LogUtil.getLogger().logError(e);
            return null;
        }
        
        final CommentLocator locator = new CommentLocator(source);   
        
        for (final CommentRange jmlCommentRange : locator.findJMLCommentRanges()) {
            
            // Search for the correct CommentRange containing our IASTNode that is supposed to be resolved.
            if(jmlCommentRange.getBeginOffset() < identifier.getStartOffset() && jmlCommentRange.getEndOffset() >= identifier.getEndOffset()) {
                
                // parse JML comment.
                final IJMLParser jmlParser = JMLPreferencesHelper.getProjectActiveJMLProfile(compilationUnit.getJavaProject().getProject()).createParser();
                IASTNode jml = null;
                try {
                    jml = jmlParser.parse(source, jmlCommentRange);
                }
                catch (final ParserException e) {
                    LogUtil.getLogger().logError(e);
                    return null;
                }
                
                // Map the JML comment to the corresponding JDT comment.
                for (final Comment comment : jdtCommentList) {
                    // check if we got the correct JDT comment
                    if (jmlCommentRange.getBeginOffset() == comment.getStartPosition()) {
                        jdtComment = comment;
                        jmlComment = jml;
                        break;
                    }
                }
                // Go out of the for loop, because we found the correct jml comment.
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
        
        // now we have all the information we need - build the result
        final ASTNode context = commentToAST.get(jdtComment);
        originalContext = context;

        // TODO: check if, what we are looking for is in another file
        final Map<String, IASTNode> jmlContext = jmlComment.traverse(new INodeTraverser<Map<String, IASTNode>>() {
            @Override
            public Map<String, IASTNode> traverse(final IASTNode node, final Map<String, IASTNode> existing) {
                if(node.getType() == ExpressionNodeTypes.MEMBER_ACCESS) {
                    //node
                }
                if(node.containsOffset(identifier.getStartOffset())) {
                    // we found the node, that contains what we are looking for
                } 
                
                return existing;
            }
        }, new HashMap<String, IASTNode>());
        
       
        
        //if(jmlContext.containsKey(key))
        
        //if(jmlContext) {
        // ~>     
        //}
        // call the recursive function, that finds the identifier and searches for it
        // in the given context first
        jdtNode = findIdentifier(context, resolveString, null);

        // well... i guess it could not be resolved.
        if(jdtNode == null) {
            return null;
        }
        
        return new ResolveResult(jdtNode, getResolveType(jdtNode), resolveBinding(jdtNode));
    }
    
    /** Get the JDT ASTNode corresponding to the given name.
     * 
     * @param context the JDT context to look for the identifier in
     * @param name the name, that we are looking for
     * @param except the ASTNode, we are skipping in our search. If set, we automatically skip all parameter declarations.
     * @return the ASTNode corresponding to the given name.
     */
    private ASTNode findIdentifier(final ASTNode context, final String name, final ASTNode except) {
        ASTNode workingContext = context; 
        ASTNode jdt = findIdentifierInContext(context, name, except);
        while(context != null) {
            if(jdt != null) {
                return jdt;
            }
            jdt = findIdentifierInContext(workingContext.getParent(), name, workingContext);
            workingContext = workingContext.getParent();
        }
        return jdt;
    }
    
    /** Get the JDT ASTNode corresponding to the given name in the given context.
     * 
     * @param context the JDT context to look for the identifier in
     * @param name the name, that we are looking for
     * @param except the ASTNode, we are skipping in our search. If set, we automatically skip all parameter declarations.
     * @return the ASTNode corresponding to the given name in the given context.
     */
    private ASTNode findIdentifierInContext(final ASTNode context, final String name, final ASTNode except) {
        
        if(context == null || context == except || name == null) {
            return null;
        }
        
        // TYPE DECLERATION
        if(context instanceof TypeDeclaration) {
            if(((TypeDeclaration) context).getName().getIdentifier().equals(name)) {
                return context;
            }
            
            for(final FieldDeclaration field : ((TypeDeclaration) context).getFields()) {
                final ASTNode result = findIdentifierInContext(field, name, except);
                if(result != null) {
                    return result;
                }
            }
            
            for(final MethodDeclaration method : ((TypeDeclaration) context).getMethods()) {
                final ASTNode result = findIdentifierInContext(method, name, except);
                if(result != null) {
                    return result;
                }
            }
            
        // METHOD DECLERATION
        } else if(context instanceof MethodDeclaration) {
            if(((MethodDeclaration) context).getName().getIdentifier().equals(name)) {
                return checkMethodDecleration((MethodDeclaration) context);
            } else {
                if(except == null && !((MethodDeclaration) context).isConstructor()) {
                    for(final Object parameter : ((MethodDeclaration) context).parameters()) {
                        final ASTNode result = findIdentifierInContext((SingleVariableDeclaration) parameter, name, except);
                        if(result != null) {
                            return result;
                        }
                    }
                }
            }
            
        // FIELD DECLERATION
        } else if(context instanceof FieldDeclaration) {
            for(final Object fragment : ((FieldDeclaration) context).fragments()) {
                final ASTNode result = findIdentifierInContext((VariableDeclarationFragment) fragment, name, except);
                if(result != null) {
                    return result;
                }
            }
            
        //SingleVariableDeclaration
        } else if(context instanceof SingleVariableDeclaration) {
            if(((SingleVariableDeclaration) context).getName().getIdentifier().equals(name)) {
                return context;
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

    /** Check the MethodDeclaration, if it matches the one we are Searching for.
     * 
     * @param resolver is the context information we need to get the types of the parameters
     * @param context 
     * @return
     */
    private ASTNode checkMethodDecleration(final MethodDeclaration context) {

        // if the name isn't correct.. we don't need to check any further
        if(!resolveString.equals(context.getName().getIdentifier())) {
            return null;
        }
        
        // This finds the Parameters for the method call in the JML comment
        final List<IASTNode> parameters = jmlComment.traverse(new INodeTraverser<List<IASTNode>>() {
            @Override
            public List<IASTNode> traverse(final IASTNode node, final List<IASTNode> parameters) {
                final List<IASTNode> children = node.getChildren();
                if( children.size() == 2 && 
                    children.get(0).getStartOffset() == identifier.getStartOffset() && 
                    children.get(0).getEndOffset() == identifier.getEndOffset()) {
                    // We found the identifier. This must be the first child.
                    // Now.. the 2nd child must be the parameter list.
                    parameters.addAll(children.get(1).getChildren().get(0).getChildren().get(0).getChildren());
                }
                return parameters;
            }
        }, new ArrayList<IASTNode>());
        
        // if the parameter count differs.. this method can not be the one we are searching for.
        if(parameters.size() != context.parameters().size()) {
            return null;
        }
        
        // if there are no parameters, it must be the correct one.
        if(parameters.size() == 0) {
            return context;
        }
        
        // we have to check the types of the parameters .. 
        for(int i = 0; i < parameters.size() ; i++) {
            // TODO: check parameters by the type checker.
            // ITypeBinding = Typecheck(parameters.get(i));
            
            // TODO: We assume, that there is nothing to be evaluated for now.
            
            
            final ASTNode jdt = findIdentifier(originalContext, getString(parameters.get(i).getChildren().get(0).getChildren().get(0)), null);
            // if it couldn't be resolved.. we can not say what type it is.
            if(jdt == null) {
                return null;
            }

            final IBinding b1 = resolveBinding((ASTNode) context.parameters().get(i));
            final IBinding b2 = resolveBinding(jdt);
            
            if(!hasSameType(b1, b2)) {
                return null;
            }
        }
        return context;
    }
    
    private boolean hasSameType(final IBinding b1, final IBinding b2) {
        final ITypeBinding type1 = getTypeFromBinding(b1);
        final ITypeBinding type2 = getTypeFromBinding(b2);
        return type1.equals(type2);
    }
    private ITypeBinding getTypeFromBinding(final IBinding binding) {
        if(binding instanceof IVariableBinding) {
            return ((IVariableBinding) binding).getType();
        } else if(binding instanceof IMethodBinding) {
            return ((IMethodBinding) binding).getReturnType();
        }
        return null;
    }

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
        }
        return binding;
    }
    
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
    
    private String getString(final IASTNode identifier) {
        return ((IStringNode)identifier).getString();
    }
    
}