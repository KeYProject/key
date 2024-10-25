/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ElseBranch;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record IfExpression(Expr condition, ThenBranch thenExpr, @Nullable ElseBranch elseExpr) implements Expr, ElseBranch {
    @Override
    public void visit(Visitor v) {
        v.performActionOnIfExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return condition;
        if (n == 1) return thenExpr;
        if (n == 2 && elseExpr != null) return elseExpr;
        throw new IndexOutOfBoundsException("IfExpression has less than " + n + " children");
    }

    @Override
    public int getChildCount() {
        return 2 + (elseExpr == null ? 0 : 1);
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("if ").append(condition).append(thenExpr);
        if (elseExpr != null) sb.append(" else ").append(elseExpr);
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        return thenExpr.type(services);
    }
}
