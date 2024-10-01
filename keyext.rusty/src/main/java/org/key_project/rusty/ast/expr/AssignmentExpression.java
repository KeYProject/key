/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record AssignmentExpression(Expr lhs, Expr rhs) implements Expr {


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
}
