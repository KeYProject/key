/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record ArithLogicalExpression(Expr left,org.key_project.rusty.ast.expr.ArithLogicalExpression.Operator op,Expr right)implements Expr{

public enum Operator implements RustyProgramElement {
    Plus, Minus, Multiply, Divide, Modulo, BitwiseAnd, BitwiseOr, BitwiseXor, Shl, Shr;

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
        case Shl -> "<<";
        case Shr -> ">>";
        };
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Operator has no children");
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnArithLogicalOperator(this);
    }
}

    @Override
    public String toString() {
        return left.toString() + " " + op + " " + right.toString();
    }

    @Override
    public int getChildCount() {
        return 3;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
        case 0 -> left;
        case 1 -> op;
        case 2 -> right;
        default -> throw new IndexOutOfBoundsException(
            "ArithLogicalExpression has only 3 children");
        };
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnArithLogicalExpression(this);
    }
}
