/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.PrimitiveType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;

import org.jspecify.annotations.NonNull;

public record ComparisonExpression(Expr left, Operator op, Expr right) implements Expr {
    @Override
    public void visit(Visitor v) {
        v.performActionOnComparisonExpression(this);
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        return switch (n) {
            case 0 -> left;
            case 1 -> op;
            case 2 -> right;
            default -> throw new IndexOutOfBoundsException(
                    "ComparisonExpression has only 3 children");
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
        return PrimitiveType.BOOL;
    }

    public enum Operator implements RustyProgramElement {
        Equal, NotEqual, Greater, Less, GreaterOrEqual, LessOrEqual;

        @Override
        public String toString() {
            return switch (this) {
                case Equal -> "==";
                case NotEqual -> "!=";
                case Greater -> ">";
                case Less -> "<";
                case GreaterOrEqual -> ">=";
                case LessOrEqual -> "<=";
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
v.performActionOnComparisonOperator(this);
        }
    }}
