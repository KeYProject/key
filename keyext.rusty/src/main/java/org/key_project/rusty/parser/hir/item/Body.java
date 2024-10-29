package org.key_project.rusty.parser.hir.item;

import org.key_project.rusty.parser.hir.expr.Expr;

import java.util.Arrays;

public record Body(Param[] params, Expr value) {
    @Override
    public String toString() {
        return "Body{" +
                "params=" + Arrays.toString(params) +
                ", value=" + value +
                '}';
    }
}
