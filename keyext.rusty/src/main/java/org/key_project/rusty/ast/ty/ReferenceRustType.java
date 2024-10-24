package org.key_project.rusty.ast.ty;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.abstraction.ReferenceType;
import org.key_project.rusty.ast.visitor.Visitor;

public record ReferenceRustType(boolean isMut, RustType inner, ReferenceType type) implements RustType {
    @Override
    public void visit(Visitor v) {
        v.performActionOnReferenceRustType(this);
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0) {return inner;}
        throw new IndexOutOfBoundsException("ReferenceRustType has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }
}
