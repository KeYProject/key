package org.key_project.rusty.ast.pat;

import org.jspecify.annotations.NonNull;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.logic.op.sv.OperatorSV;

public record SchemaVarPattern(boolean reference, boolean mut, OperatorSV operatorSV) implements Pattern {
    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return operatorSV;
        throw new IndexOutOfBoundsException("SchemaVarPattern has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }
}
