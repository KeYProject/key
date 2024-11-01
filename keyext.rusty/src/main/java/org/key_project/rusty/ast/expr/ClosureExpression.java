/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.ty.RustType;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

//spotless:off
public record ClosureExpression(boolean move, ImmutableArray<ClosureParam> params, @Nullable RustType ty,
                                Expr body) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnClosureExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (0 <= n && n < params.size()) {
            return params.get(n);
        }
        n -= params.size();
        if (n == 0 && ty != null) return ty;
        if (n == 0) return body;
        throw new IndexOutOfBoundsException("ClosureExpression has only " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        return params.size() + 1 + (ty != null ? 1 : 0);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("|");
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(params.get(i));
        }
        sb.append("|");
        if (ty != null) {
            sb.append(" -> ").append(ty);
        }
        sb.append(body);
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        throw new UnsupportedOperationException();
    }
}
//spotless:on