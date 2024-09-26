/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public class NegationExpression implements Expr {
    public enum Operator implements SyntaxElement {
        Neg, Not;

        @Override
        public String toString() {
            return switch (this) {
            case Neg -> "!";
            case Not -> "~";
            };
        }

        @Override
        public SyntaxElement getChild(int n) {
            throw new IndexOutOfBoundsException("Operator has no children");
        }

        @Override
        public int getChildCount() {
            return 0;
        }
    }

    private final Expr expr;
    private final Operator op;

    public NegationExpression(Expr expr, Operator op) {
        this.expr = expr;
        this.op = op;
    }

    public Operator getOp() {
        return op;
    }

    public Expr getExpr() {
        return expr;
    }

    @Override
    public String toString() {
        return op.toString() + expr;
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> op;
        case 1 -> expr;
        default -> throw new IndexOutOfBoundsException("NegationExpression has only 2 children");
        };
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnNegationExpression(this);
    }
}
