/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import java.util.Objects;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.SourceData;
import org.key_project.rusty.ast.abstraction.PrimitiveType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.rule.MatchConditions;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

public final class BinaryExpression implements Expr {
    private final Operator op;
    private final Expr left;
    private final Expr right;

    public BinaryExpression(Operator op, Expr left, Expr right) {
        this.op = op;
        this.left = left;
        this.right = right;
    }

    public BinaryExpression(ExtList children) {
        op = children.removeFirstOccurrence(Operator.class);
        left = children.removeFirstOccurrence(Expr.class);
        right = children.removeFirstOccurrence(Expr.class);
    }

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

    public Operator op() {
        return op;
    }

    public Expr left() {
        return left;
    }

    public Expr right() {
        return right;
    }

    @Override
    public Type type(Services services) {
        // TODO: nicer
        return switch (op) {
        case Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shr, Shl -> left.type(services);
        case And, Or, Eq, Ne, Lt, Gt, Le, Ge -> PrimitiveType.BOOL;
        };
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this)
            return true;
        if (obj == null || obj.getClass() != this.getClass())
            return false;
        var that = (BinaryExpression) obj;
        return Objects.equals(this.op, that.op) &&
                Objects.equals(this.left, that.left) &&
                Objects.equals(this.right, that.right);
    }

    @Override
    public int hashCode() {
        return Objects.hash(op, left, right);
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

        @Override
        public MatchConditions match(SourceData sourceData, MatchConditions mc) {
            final var src = sourceData.getSource();

            if (src == null)
                return null;

            if (src.getClass() != this.getClass()) {
                return null;
            }
            if (this != src)
                return null;
            sourceData.next();
            return mc;
        }
    }
}
