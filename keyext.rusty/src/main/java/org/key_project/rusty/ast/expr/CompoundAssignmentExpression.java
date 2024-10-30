/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record CompoundAssignmentExpression(Expr left, Operator op, Expr right) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnCompoundAssignmentExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
            case 0 -> left;
            case 1 -> op;
            case 2 -> right;
            default -> throw new IndexOutOfBoundsException(
                    "CompoundAssignmentExpression has only 3 children");
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

    @Override
    public Type type(Services services) {
        return TupleType.UNIT;
    }

    public enum Operator implements RustyProgramElement {
        Plus, Minus, Multiply, Divide, Modulo, And, Or, Xor, Shl, Shr;

        @Override
        public String toString() {
            return switch (this) {
                case Plus -> "+=";
                case Minus -> "-=";
                case Multiply -> "*=";
                case Divide -> "/=";
                case Modulo -> "%=";
                case And -> "&=";
                case Or -> "|=";
                case Xor -> "^=";
                case Shl -> "<<=";
                case Shr -> ">>=";
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

        @Override
        public void visit(Visitor v) {
            v.performActionOnCompoundAssignmentOperator(this);
        }
    }}
