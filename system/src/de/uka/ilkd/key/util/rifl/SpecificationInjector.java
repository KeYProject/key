// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 

package de.uka.ilkd.key.util.rifl;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

/** Writes JML* translation of RIFL specifications to Java files.
 * This is a manipulating Recoder source visitor.
 * Implementation warning: manipulating the AST before traversing it
 * may have unexpected results.
 * @author bruns
 */
public class SpecificationInjector extends SourceVisitor {
    
    private final SpecificationContainer sc;

    public SpecificationInjector(SpecificationContainer sc) {
        this.sc = sc;
    }
    
    //////////////////////////////////////////////////////////////
    // visitor methods
    //////////////////////////////////////////////////////////////
    
    @Override
    public void visitCompilationUnit (CompilationUnit cu) {
        accessChildren(cu);
        addComment(cu,"\n// JML* comment created by KeY RIFL Transformer.\n");
    }

    @Override
    public void visitClassDeclaration (ClassDeclaration cd) {
        accessChildren(cd);
    }

    @Override
    public void visitInterfaceDeclaration (InterfaceDeclaration id) {
        accessChildren(id);
    }

    @Override
    public void visitMethodDeclaration (MethodDeclaration md) {
        JMLFactory factory = new JMLFactory();
        
        // add return value
        factory.addResultToRespects(sc.returnValue(md));

        // add parameters
        for (int i= 0; i < md.getParameterDeclarationCount(); i++) {
            ParameterDeclaration pd = md.getParameterDeclarationAt(i);
            factory.addToRespects(
                    pd.getVariableSpecification().getName(),sc.parameter(md, i));
        }
        
        // add fields (TODO)
                
        addComment(md,factory.getSpecification());
    }
    
    
    //////////////////////////////////////////////////////////////
    // private methods
    //////////////////////////////////////////////////////////////
    
    private void accessChildren(JavaNonTerminalProgramElement pe) {
        for (int i= 0; i < pe.getChildCount(); i++)
            pe.getChildAt(i).accept(this);
    }

    private static void addComment(JavaProgramElement se, String comment) {
        // fixes issue with Recoder that it writes comments _after_ the element
        NonTerminalProgramElement parent = se.getASTParent();
        for (int i= 0; i < parent.getChildCount(); i++) {
            if (i > 0 && parent.getChildAt(i)==se) {
                // chose previous element
                se = (JavaProgramElement) parent.getChildAt(i-1);
            } // TODO: what if se is the 0th child ??
        }
        
        final ASTArrayList<Comment> commentList = new ASTArrayList<Comment>();
        ASTList<Comment> oldComments = se.getComments();
        if (oldComments != null) commentList.addAll(oldComments);
        commentList.add(new Comment(comment));
        se.setComments(commentList);
    }
    
    /** Produces JML* respects clauses.
     * Clauses are internally labeled with keys (resulting from security domains
     * in RIFL), which are discarded in the final output.
     * @author bruns
     */
    private static class JMLFactory {
        
        private static final String DEFAULT_INDENTATION = "  ";
        private static final String DEFAULT_KEY = "";
        private static final String RESULT = "\\result";
        private static final String RESPECTS = "respects";
        private static final String JML_END = "@*/";
        private static final String JML_START = "/*@ ";
        
        private final String indentation;
        private final Map<String,List<String>> respects = new HashMap<String, List<String>>();
        
        JMLFactory () {
            indentation = DEFAULT_INDENTATION;
        }
        
        JMLFactory (int indent) {
            StringBuffer sb = new StringBuffer();
            for (int i= 0; i<indent; i++)
                sb.append(' ');
            indentation = sb.toString();
        }
        
        private void put (String key, String value) {
            if (key == null) return;
            List<String> target = respects.get(key);
            if (target == null) {
                target = new ArrayList<String>();
                respects.put(key, target);
            }
            target.add(value);
        }
        
        // TODO allow more respects clauses
        
        void addToRespects(String name, String key){
            put(key, name);
        }
        
        void addToRespects(String name){
            put(DEFAULT_KEY, name);
        }
        
        /** Adds \result to a respects clause labeled by key. */
        void addResultToRespects(String key){
            put(key, RESULT);
        }
        
        void addResultToRespects(){
            put(DEFAULT_KEY, RESULT);
        }
        
        /** Gets a formatted JML comment.*/
        String getSpecification() {
            // start JML
            StringBuffer sb = new StringBuffer(indentation);
            sb.append(JML_START+"\n");

            // respects clauses
            for (List<String> oneRespect: respects.values()) {
                sb.append(indentation);
                sb.append(DEFAULT_INDENTATION);
                sb.append("@ ");
                sb.append(RESPECTS);
                for (String elem: oneRespect) {
                    sb.append(" ");
                    sb.append(elem);
                    sb.append(",");
                }
                sb.deleteCharAt(sb.length()-1);
                sb.append(";\n");
            }
            
            // close JML
            sb.append(indentation);
            sb.append(DEFAULT_INDENTATION);
            sb.append(JML_END);
            return sb.toString();
        }
    }
    
}
