/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.Operator;

public class ArithLogicalExpression implements Expr {
    public enum Operator {
        Plus, Minus, Multiply, Divide, Modulo, BitwiseAnd, BitwiseOr, BitwiseXor;

        @Override
        public String toString() {
            return switch (this) {
            case Plus -> "+";
            case Minus -> "-";
            case Multiply -> "*";
            case Divide -> "/";
            case Modulo -> "%";
            case BitwiseAnd -> "&";
            case BitwiseOr -> "|";
            case BitwiseXor -> "^";
            };
        }
    }

    private final Expr left;
    private final Expr right;
    private final Operator op;

    public ArithLogicalExpression(Expr left, Operator op, Expr right) {
        this.left = left;
        this.op = op;
        this.right = right;
    }

    @Override
    public String toString() {
        return left.toString() + " " + op + " " + right.toString();
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> left;
        case 1 -> right;
        default -> throw new IndexOutOfBoundsException(
            "ArithLogicalExpression has only 2 children");
        };
    }
}
