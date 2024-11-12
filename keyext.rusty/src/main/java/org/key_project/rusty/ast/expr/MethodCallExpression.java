/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

//spotless:off
public record MethodCallExpression(Expr callee, org.key_project.rusty.ast.PathExprSegment method,
                                   ImmutableArray<Expr> params) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnMethodCall(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return callee;
        }
        --n;
        if (n == 0) {
            return method;
        }
        --n;
        return params.get(n);
    }

    @Override
    public int getChildCount() {
        return 2 + params.size();
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append(callee).append(".").append(method).append("(");
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) {
                sb.append(", ");
            }
            sb.append(params.get(i));
        }
        sb.append(")");
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        throw new UnsupportedOperationException();
    }
}
//spotless:on