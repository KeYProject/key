package org.key_project.llmsynth.jml;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.jml.NodeWithContracts;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.visitor.CloneVisitor;
import com.github.javaparser.ast.visitor.Visitable;

public abstract class AbstractLoopVisitor extends CloneVisitor {
    public AbstractLoopVisitor() {
        super();
    }

    protected abstract <T extends Node & NodeWithContracts<T>> T visitLoop(T n, T result);

    @Override
    public Visitable visit(WhileStmt n, Object arg) {
        WhileStmt result = (WhileStmt) super.visit(n, arg);
        return visitLoop(n, result);
    }

    @Override
    public Visitable visit(ForStmt n, Object arg) {
        ForStmt result = (ForStmt) super.visit(n, arg);
        return visitLoop(n, result);
    }

    @Override
    public Visitable visit(ForEachStmt n, Object arg) {
        ForEachStmt result = (ForEachStmt) super.visit(n, arg);
        return visitLoop(n, result);
    }

    @Override
    public Visitable visit(DoStmt n, Object arg) {
        DoStmt result = (DoStmt) super.visit(n, arg);
        return visitLoop(n, result);
    }
}
