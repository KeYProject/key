package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Path;
import org.key_project.rusty.ast.Res;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

public record PathExpr(Path<Res> path, Type type) implements Expr {
    @Override
    public Type type(Services services) {
        return type;
    }

    @Override
    public void visit(Visitor v) {

    }

    @Override
    public SyntaxElement getChild(int n) {
        return null;
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
