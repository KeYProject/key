package de.uka.ilkd.key.util.rifl;

import java.util.ArrayList;
import java.util.List;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class SpecificationInjector extends SourceVisitor {

    public SpecificationInjector() {
        // TODO Auto-generated constructor stub
    }
    
    //////////////////////////////////////////////////////////////
    // visitor methods
    //////////////////////////////////////////////////////////////
    
    @Override
    public void visitCompilationUnit (CompilationUnit cu) {
        accessChildren(cu);
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
        addComment(md,"/* test */");
        // do not go down anymore
    }
    
    
    //////////////////////////////////////////////////////////////
    // private methods
    //////////////////////////////////////////////////////////////
    
    private void accessChildren(JavaNonTerminalProgramElement pe) {
        for (int i= 0; i < pe.getChildCount(); i++)
            pe.getChildAt(i).accept(this);
    }

    private static void addComment(JavaProgramElement se, String comment) {
        // TODO: place comments more appropriately
        final ASTArrayList<Comment> commentList = new ASTArrayList<Comment>();
        ASTList<Comment> oldComments = se.getComments();
        if (oldComments != null) commentList.addAll(oldComments);
        commentList.add(new Comment(comment));
        se.setComments(commentList);
    }
    
    private static class JMLWriter {
        
        private static final String RESULT = "\\result";
        private static final String RESPECTS = "respects";
        private static final String JML_END = "@*/";
        private static final String JML_START = "/*@ ";
        
        private JavaProgramElement se;
        private List<String> respects = new ArrayList<String>();
        
        JMLWriter (JavaProgramElement se) {
            this.se = se;
        }
        
        void clear () {
            respects = new ArrayList<String>();
        }
        
        void addToRespects(de.uka.ilkd.key.util.rifl.SpecificationEntity.Field f){
            respects.add(f.toString());
        }
        
        void addResultToRespects(){
            respects.add(RESULT);
        }
        
        String getSpecification() {
            // start JML
            StringBuffer sb = new StringBuffer("// JML* comment created by KeY RIFL Transformer.\n");
            sb.append(JML_START);

            // respects clause
            if (!respects.isEmpty()) {
                sb.append(RESPECTS);
                for (String elem: respects) {
                    sb.append(" ");
                    sb.append(elem);
                    sb.append(",");
                }
                sb.deleteCharAt(sb.length()-1);
                sb.append(";\n");
            }
            
            // close JML
            indent(sb);
            sb.append(JML_END);
            return sb.toString();
        }
        
        private void indent (StringBuffer sb) {
            sb.append("  ");
        }
    }
    
}
