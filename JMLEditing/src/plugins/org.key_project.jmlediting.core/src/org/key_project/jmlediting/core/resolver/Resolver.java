/**
 * @author Christopher Beckmann
 */
package org.key_project.jmlediting.core.resolver;

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
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.core.dom.VariableDeclarationFragment;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.util.jdt.JDTUtil;

/**
 * The Resolver class, that only has a static method "resolve" that will resolve the {@link IASTNode} given and find the corresponding JavaElement or JML decleration.
 * 
 * 
 * @author Christopher Beckmann
 * 
 * @noextend This class it not supposed to be subclassed.
 * @noinstantiate This class is not supposed to be instantiated.
 */
public final class Resolver {
    
    /**
     * Constructor is private, because this class is not supposed to be instantiated.
     */
    private Resolver() {}
    
    /**
     * Resolves an identifier inside of a JML comment. 
     * It will find the JavaElement or JML Element the {@link IASTNode} is referring to. 
     * If it can not find the JavaElement or JML element, it will return null.
     * 
     * @param cu 
     *      is the {@link ICompilationUnit} of the file, the {@link IASTNode} to be resolved is in
     * @param toResolve
     *      is the {@link IASTNode} of the identifier, that will be resolved. Possible children nodes are ignored.
     * @return a {@link ResolveResult} with the resolve information for that {@link IASTNode}, if it was able to be resolved.
     *         Otherwise it will return null.
     * @throws JavaModelException
     * @throws ParserException 
     */
    public static ResolveResult resolve(final ICompilationUnit cu, IASTNode toResolve) throws JavaModelException, ParserException {

        // TODO: check if the given IASTNode is correct and get possible information
        if(toResolve == null || cu == null) {
            return null;
        }
        
        System.out.println(((IStringNode)toResolve).getString());
        String name = ((IStringNode)toResolve).getString();
        
        // Parse JML and map nodes to JDT
        Comment jdtComment = null;
        IASTNode jmlComment = null;        
        final  Map<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();
        
        // Parse JDT
        final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(cu);
        
        // Get all the JDT comments so we can find the correct one.
        @SuppressWarnings("unchecked")
        final List<Comment> jdtCommentList = jdtAST.getCommentList();
        
        // Locate the comments
        CommentLocator locator = new CommentLocator(cu.getSource());   
        
        for (final CommentRange jmlCommentRange : locator.findJMLCommentRanges()) {
            
            // Search for the correct CommentRange containing our IASTNode that is supposed to be resolved.
            if(jmlCommentRange.getBeginOffset() > toResolve.getStartOffset() && toResolve.getEndOffset() <= jmlCommentRange.getEndOffset()) {
                
                // parse JML comment.
                IJMLParser jmlParser = JMLPreferencesHelper.getProjectActiveJMLProfile(cu.getJavaProject().getProject()).createParser();
                IASTNode jml = jmlParser.parse(cu.getSource(), jmlCommentRange);
                
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
                        Comment comment = jdtCommentList.get(pos);
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
        ASTNode context = commentToAST.get(jdtComment);

        // call the recursive function, that finds the identifier in the given context
        ASTNode jdtNode = findIdentifier(context, name, null);
        
        // if we weren't able to find it here.. we go up step by step
        while(jdtNode == null) {
            if(context == null) {
                break;
            }
            jdtNode = findIdentifier(context.getParent(), name, context);
            context = context.getParent();
        }
        // well... i guess it could not be resolved.
        if(jdtNode == null) {
            return null;
        }
        
        IBinding binding = null;
        ResolveResultType type = ResolveResultType.UNSPECIFIED;

        if(jdtNode instanceof TypeDeclaration) {
            binding = ((TypeDeclaration) jdtNode).resolveBinding();
            type = ResolveResultType.CLASS;
        } else if(jdtNode instanceof MethodDeclaration) {
            binding = ((MethodDeclaration) jdtNode).resolveBinding();
            type = ResolveResultType.METHOD;
        } else if(jdtNode instanceof SingleVariableDeclaration) {
            binding = ((SingleVariableDeclaration) jdtNode).resolveBinding();
            type = ResolveResultType.FIELD;
        } else if(jdtNode instanceof VariableDeclarationFragment) {
            binding = ((VariableDeclarationFragment) jdtNode).resolveBinding();
            type = ResolveResultType.PARAMETER;
        }
        
        return new ResolveResult(jdtNode, type, binding);
    }
    
    private static ASTNode findIdentifier(ASTNode context, String name, ASTNode except) {
        
        if(context == null || context == except || name == null) {
            return null;
        }
        
        // TYPE DECLERATION
        if(context instanceof TypeDeclaration) {
            if(((TypeDeclaration) context).getName().getIdentifier().equals(name)) {
                return findIdentifier(context, name, except);
            }
            
            for(FieldDeclaration field : ((TypeDeclaration) context).getFields()) {
                ASTNode result = findIdentifier(field, name, except);
                if(result != null) {
                    return result;
                }
            }
            
            for(MethodDeclaration method : ((TypeDeclaration) context).getMethods()) {
                ASTNode result = findIdentifier(method, name, except);
                if(result != null) {
                    return result;
                }
            }
            
        // METHOD DECLERATION
        } else if(context instanceof MethodDeclaration) {
            if(((MethodDeclaration) context).getName().getIdentifier().equals(name)) {
                return context;
            } else {
                if(!((MethodDeclaration) context).isConstructor()) {
                    for(Object parameter : ((MethodDeclaration) context).parameters()) {
                        ASTNode result = findIdentifier(((SingleVariableDeclaration) parameter), name, except);
                        if(result != null) {
                            return result;
                        }
                    }
                }
                return null;
            }
            
        // FIELD DECLERATION
        } else if(context instanceof FieldDeclaration) {
            for(Object fragment : ((FieldDeclaration) context).fragments()) {
                ASTNode result = findIdentifier(((VariableDeclarationFragment) fragment), name, except);
                if(result != null) {
                    return result;
                }
            }
            return null;
            
        //SingleVariableDeclaration
        } else if(context instanceof SingleVariableDeclaration) {
            if(((SingleVariableDeclaration) context).getName().getIdentifier().equals(name)) {
                return context;
            }
            return null;
            
        //VariableDeclarationFragment
        } else if(context instanceof VariableDeclarationFragment) {
            if(((VariableDeclarationFragment) context).getName().getIdentifier().equals(name)) {
                return context;
            }
            return null;
        }
        // NOTHING FOUND
        return null;
    }
    
}