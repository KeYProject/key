/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.fn;

import java.util.Objects;
import java.util.stream.Collectors;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.Item;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

//spotless:off
public record Function(Name name, org.key_project.util.collection.ImmutableArray<FunctionParam> params,
                       RustType returnType, BlockExpression body) implements Item, Named {

    @Override
    public int getChildCount() {
        return 3 + params.size();
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (0 <= n && n < params.size()) return Objects.requireNonNull(params.get(n));
        n -= params.size();
        if (n == 0) return returnType;
        if (n == 1) return body;
        throw new IndexOutOfBoundsException("No child at index " + n);
    }

    @Override
    public String toString() {
        return "fn " + name() + "(" + params.stream().map(Object::toString).collect(Collectors.joining(", ")) + ") -> " + returnType + " " + body;
    }

    @Override
    public void visit(Visitor v) {
        throw new RuntimeException("TODO @ DD");
    }
}
//spotless:on