/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

public record ReturnExpression(@Nullable Expr expr) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnReturnExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0 && expr != null) {return expr;}
        throw new IndexOutOfBoundsException("ReturnExpression has only " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        int c =0;
        if (expr != null) {++c;}
        return c;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("return");
        if (expr != null) {
            sb.append(" ").append(expr);
        }
        return sb.toString();
    }
}
