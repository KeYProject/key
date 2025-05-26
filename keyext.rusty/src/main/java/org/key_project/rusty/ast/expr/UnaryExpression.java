/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.abstraction.PrimitiveType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

public final class UnaryExpression implements Expr {
    private final Operator op;
    private final Expr expr;

    public UnaryExpression(Operator op, Expr expr) {
        this.op = op;
        this.expr = expr;
    }

    public UnaryExpression(ExtList children) {
        op = children.removeFirstOccurrence(Operator.class);
        expr = children.removeFirstOccurrence(Expr.class);
    }

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
        return switch(n){case 0->op;case 1->expr;default->throw new IndexOutOfBoundsException("UnaryExpression has only 2 children");};
    }

    @Override
    public int getChildCount() {
        return 2;
    }

    @Override
    public String toString() {
        return op.toString() + expr;
    }

    public Operator op() {
        return op;
    }

    public Expr expr() {
        return expr;
    }

    @Override
    public Type type(Services services) {
        return switch (op) {
        case Neg -> expr.type(services);
        case Not -> PrimitiveType.BOOL;
        case Deref -> null;
        };
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (UnaryExpression) obj;
        return Objects.equals(this.op, that.op) &&
                Objects.equals(this.expr, that.expr);
    }

    @Override
    public int hashCode() {
        return Objects.hash(op, expr);
    }

}
