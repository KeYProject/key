/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.ReferenceType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

// spotless:off
public class BorrowExpression implements Expr {
    private final boolean mut;
    private final Expr expr;

    public BorrowExpression(boolean mut, Expr expr) {
        this.mut = mut;
        this.expr = expr;
    }

    public BorrowExpression(boolean mut, ExtList children) {
        this.mut = mut;
        this.expr = children.get(Expr.class);
    }

    public boolean isMut() {
        return mut;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnBorrowExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) return expr;
        throw new IndexOutOfBoundsException("BorrowExpression has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("&");
        if (mut) sb.append("mut ");
        sb.append(expr);
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        return ReferenceType.get(expr.type(services), mut);
    }

    @Override
    public boolean equals(Object o) {
        if (o == null || getClass() != o.getClass()) return false;
        BorrowExpression that = (BorrowExpression) o;
        return mut == that.mut && Objects.equals(expr, that.expr);
    }

    @Override
    public int hashCode() {
        return Objects.hash(mut, expr);
    }
}
//spotless:on
