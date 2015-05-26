/**
 * 
 * 
 * @author Christopher Beckmann
 *
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
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.MethodDeclaration;
import org.eclipse.jdt.core.dom.SingleVariableDeclaration;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.util.jdt.JDTUtil;

public abstract class Resolver {

    
    public static List<ResolveResult> resolve(final ICompilationUnit cu) throws JavaModelException {
        
        // TODO: save spec_public and other visibility specifiers, because they may be visible although they are not accessible.
        // TODO: may have to resolve every class, before we can tell if something is not resolvable :( 
        
        // Parse JDT
        final CompilationUnit jdtAST = (CompilationUnit) JDTUtil.parse(cu);

        // Parse JML and map nodes to JDT Comments
        final  Map<IASTNode, Comment> jmlToComment = new HashMap<IASTNode, Comment>();
        final  Map<Comment, ASTNode> commentToAST = new HashMap<Comment, ASTNode>();

        // Get all the JDT comments so we can map them.
        @SuppressWarnings("unchecked")
        final List<Comment> commentList = jdtAST.getCommentList();
        
        // start parsing JML
        final List<IASTNode> iAstList = new ArrayList<IASTNode>();
        CommentLocator locator = null;
        locator = new CommentLocator(cu.getSource());   // locate the comments
        for (final CommentRange jmlComment : locator.findJMLCommentRanges()) {
            IJMLParser jmlParser = JMLPreferencesHelper.getProjectActiveJMLProfile(cu.getJavaProject().getProject()).createParser();
            IASTNode jml = null;
            
            try {
                jml = jmlParser.parse(cu.getSource(), jmlComment);
                iAstList.add(jml);
            }
            catch (ParserException e) {
            }
            
            // Map the JML comment to the corresponding JDT comment.
            for (final Comment jdtComment : commentList) {
                if (jml != null && jmlComment.getBeginOffset() == jdtComment.getStartPosition()) {
                    jmlToComment.put(jml, jdtComment);
                    break;
                }
            } 
        }
        
        jdtAST.accept(new ASTVisitor() {
            @Override
            public boolean preVisit2(final ASTNode node) {
                final int start = jdtAST.firstLeadingCommentIndex(node);
                if (start != -1) {
                    int pos = start;
                    while (pos < commentList.size()
                            && commentList.get(pos).getStartPosition() < node.getStartPosition()) {
                        Comment comment = commentList.get(pos);
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
        
        // get everything that is a String
        List<IASTNode> unresolvedJML = new ArrayList<IASTNode>();
        //final  Map<IASTNode, IASTNode> unresolvedToJML = new HashMap<IASTNode, IASTNode>();
        
        // * * * * * * * Now, finally we get to resolve stuff. :)
        // Start with creating the result list.
        List<ResolveResult> result = new ArrayList<ResolveResult>();
        // now we check the jml comments for unresolved strings        
        for(IASTNode jml : iAstList) {
            
            ASTNode astNode = commentToAST.get(jmlToComment.get(jml));
            IBinding binding = null;
            for(IASTNode jmlNode : Nodes.getAllNodesOfType(jml, NodeTypes.STRING)) {
                if(astNode instanceof TypeDeclaration) {
                    binding = ((TypeDeclaration) astNode).resolveBinding();
                    //((IMethodBinding)binding).;
                } else if(astNode instanceof MethodDeclaration) {
                    binding = ((MethodDeclaration) astNode).resolveBinding();
                } else if(astNode instanceof SingleVariableDeclaration) {
                    binding = ((SingleVariableDeclaration) astNode).resolveBinding();
                }
                //TODO: save stuff and add a ResolveResult to the list.
            }
            
            
            unresolvedJML.addAll(Nodes.getAllNodesOfType(jml, NodeTypes.STRING));
            
        }
        
        for(IASTNode jml : unresolvedJML) {
            System.out.println(jml.prettyPrintAST());
        }
        
        //ResolveHelper rh = new ResolveHelper(iAstList);
        //jdtAST.accept(rh);
        
        // ResolveResult als BaumStruktur? ähnlich zu ASTNodes ?
        // Vielleicht die IAST Struktur erweitern und alle StringNodes mit Klassen ersetzen, die Informationen
        //      zum resolving halten. -> Scheint beste Idee bisher ?
        // Eine Klasse, die alle Informationen über alle Variablen und Methoden deklerationen bekommt?
        // Resolver benutzung.. ICompilationUnit übergeben ok? , andere übergabe werte?
        // Resolver statische Methoden?

        return result;
    }
}