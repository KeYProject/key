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
public record BinaryExpression(Operator op, Expr left, Expr right, Type type) implements Expr {
      @Override
    public void visit(Visitor v) {
        v.performActionOnBinaryExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
            case 0 -> left;
            case 1 -> op;
            case 2 -> right;
            default -> throw new IndexOutOfBoundsException("BinaryExpression has only 3 children");
        };
    }

    @Override
    public int getChildCount() {
        return 3;
    }

    @Override
    public String toString() {
        return left + " " + op + " " + right;
    }

    public enum Operator implements RustyProgramElement {
        Add("+"),
        Sub("-"),
        Mul("-"),
        Div("/"),
        Rem("%"),
        And("&&"),
        Or("||"),
        BitXor("^"),
        BitAnd("&"),
        BitOr("|"),
        Shl("<<"),
        Shr(">>"),
        Eq("=="),
        Lt("<"),
        Le("<="),
        Ne("!="),
        Ge(">="),
        Gt(">");

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
            v.performActionOnBinaryOperator(this);
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
}
//spotless:on
