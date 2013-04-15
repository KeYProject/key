package de.uka.ilkd.key.util.rifl;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;

public class SpecificationInjector extends SourceVisitor {

    public SpecificationInjector() {
        // TODO Auto-generated constructor stub
    }
    
    @Override
    public void visitCompilationUnit (CompilationUnit cu) {
        accessChildren(cu);
    }

    @Override
    public void visitClassDeclaration (ClassDeclaration cd) {
        accessChildren(cd);
        addComment(cd,"/* test */");
    }

    @Override
    public void visitInterfaceDeclaration (InterfaceDeclaration id) {
        accessChildren(id);
    }

    @Override
    public void visitMethodDeclaration (MethodDeclaration md) {
        // do not go down anymore
    }
    
    private void accessChildren(JavaNonTerminalProgramElement pe) {
        for (int i= 0; i < pe.getChildCount(); i++)
            pe.getChildAt(i).accept(this);
    }

    private static void addComment(JavaProgramElement se, String comment) {
        final ASTArrayList<Comment> commentList = new ASTArrayList<Comment>();
        ASTList<Comment> oldComments = se.getComments();
        if (oldComments != null) commentList.addAll(oldComments);
        commentList.add(new Comment(comment));
        se.setComments(commentList);
    }
    
}
