/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.ElseBranch;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public final class IfExpression implements Expr, ElseBranch {
    private final Expr condition;
    private final ThenBranch thenExpr;
    private final @Nullable ElseBranch elseExpr;
    private final Type type;

    public IfExpression(Expr condition, ThenBranch thenExpr,
            @Nullable ElseBranch elseExpr, Type type) {
        this.condition = condition;
        this.thenExpr = thenExpr;
        this.elseExpr = elseExpr;
        this.type = type;
    }

    public IfExpression(Services services, ExtList children) {
        condition = children.removeFirstOccurrence(Expr.class);
        thenExpr = children.removeFirstOccurrence(ThenBranch.class);
        elseExpr = children.removeFirstOccurrence(ElseBranch.class);
        type = thenExpr.type(services);
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnIfExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0)
            return condition;
        if (n == 1)
            return thenExpr;
        if (n == 2 && elseExpr != null)
            return elseExpr;
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
        if (elseExpr != null)
            sb.append(" else ").append(elseExpr);
        return sb.toString();
    }

    public Expr condition() {
        return condition;
    }

    public ThenBranch thenExpr() {
        return thenExpr;
    }

    public @Nullable ElseBranch elseExpr() {
        return elseExpr;
    }

    @Override
    public Type type(Services services) {
        return type;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (IfExpression) obj;
        return Objects.equals(this.condition, that.condition) &&
                Objects.equals(this.thenExpr, that.thenExpr) &&
                Objects.equals(this.elseExpr, that.elseExpr) &&
                Objects.equals(this.type, that.type);
    }

    @Override
    public int hashCode() {
        return Objects.hash(condition, thenExpr, elseExpr, type);
    }

}
