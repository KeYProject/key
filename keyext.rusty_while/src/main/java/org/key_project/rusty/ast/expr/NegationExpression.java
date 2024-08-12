/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;

import org.jspecify.annotations.NonNull;
import org.key_project.rusty.ast.visitor.Visitor;

public class NegationExpression implements Expr {
    public enum Operator {
        Neg, Not;

        @Override
        public String toString() {
            return switch (this) {
            case Neg -> "!";
            case Not -> "~";
            };
        }
    }

    private final Expr expr;
    Operator op;

    public NegationExpression(Expr expr) {
        this.expr = expr;
    }

    @Override
    public String toString() {
        return op.toString() + expr;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return expr;
        }
        throw new IndexOutOfBoundsException(
            "NegationExpression has only 1 children");
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnNegationExpression(this);
    }
}
