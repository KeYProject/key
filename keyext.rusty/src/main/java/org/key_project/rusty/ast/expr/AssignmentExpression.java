/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Arrays;
import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

public final class AssignmentExpression implements Expr {
    private final Expr lhs;
    private final Expr rhs;

    public AssignmentExpression(Expr lhs, Expr rhs) {
        this.lhs = lhs;
        this.rhs = rhs;
    }

    public AssignmentExpression(ExtList changeList) {
        Expr[] exprs = changeList.collect(Expr.class);
        assert exprs.length == 2 : Arrays.toString(exprs);
        lhs = exprs[0];
        rhs = exprs[1];
    }


    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> lhs;
        case 1 -> rhs;
        default -> throw new IndexOutOfBoundsException(
            "AssignmentExpression has only two children");
        };
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        return lhs + " = " + rhs;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnAssignmentExpression(this);
    }

    public Expr lhs() {
        return lhs;
    }

    public Expr rhs() {
        return rhs;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (AssignmentExpression) obj;
        return Objects.equals(this.lhs, that.lhs) &&
                Objects.equals(this.rhs, that.rhs);
    }

    @Override
    public int hashCode() {
        return Objects.hash(lhs, rhs);
    }

}
