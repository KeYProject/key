/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.Label;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

//spotless:off
public record ContinueExpression(@Nullable Label label, @Nullable Expr expr) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnContinueExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0 && label != null) {
            return label;
        }
        if (label != null) {
            --n;
        }
        if (n == 0 && expr != null) {
            return expr;
        }
        throw new IndexOutOfBoundsException("ContinueExpression has only " + getChildCount() + " children");
    }

    @Override
    public int getChildCount() {
        int c = 0;
        if (label != null) {
            ++c;
        }
        if (expr != null) {
            ++c;
        }
        return c;
    }

    @Override
    public String toString() {
        StringBuilder sb = new StringBuilder();
        sb.append("continue");
        if (label != null) {
            sb.append(" ").append(label);
        }
        if (expr != null) {
            sb.append(" ").append(expr);
        }
        sb.append(";");
        return sb.toString();
    }

    @Override
    public Type type(Services services) {
        return TupleType.UNIT;
    }
}
//spotless:on