package org.key_project.rusty.ast;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;

public record Identifier(Name name) implements Named, SyntaxElement {

    @Override
    public Name name() {
        return null;
    }

    @Override
    public SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Identifier has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }
}
