/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

// spotless:off
public record UnaryExpression(Operator op, Expr expr, Type type) implements Expr {
    public enum Operator implements RustyProgramElement {
        Deref("*"),
        Not("!"),
        Neg("-"),
        ;

        private final String symbol;

        Operator(String s) {
            symbol = s;
        }

        @Override
        public String toString() {
            return symbol;
        }

        @Override
        public void visit(Visitor v) {
            v.performActionOnUnaryOperator(this);
        }

        @Override
        public @NonNull SyntaxElement getChild(int n) {
            throw new IndexOutOfBoundsException("Operator has no children");
        }

        @Override
        public int getChildCount() {
            return 0;
        }

    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnUnaryExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
            case 0 -> op;
            case 1 -> expr;
            default -> throw new IndexOutOfBoundsException("UnaryExpression has only 2 children");
        };
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        return op.toString() + expr;
    }
}
//spotless:on
