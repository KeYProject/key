/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.stmt;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public class ExpressionStatement implements Statement {
    private final Expr expression;

    public ExpressionStatement(Expr expression) {
        this.expression = expression;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return expression;
        }
        throw new IndexOutOfBoundsException("ExpressionStatement has only one child.");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        return expression.toString() + ";";
    }

    @Override
    public void visit(Visitor v) {
        expression.visit(v);
    }
}
