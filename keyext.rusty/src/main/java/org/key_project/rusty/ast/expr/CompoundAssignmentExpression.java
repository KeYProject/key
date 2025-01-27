/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.expr;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.Services;
import org.key_project.rusty.ast.abstraction.TupleType;
import org.key_project.rusty.ast.abstraction.Type;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

import org.jspecify.annotations.NonNull;

// spotless:off
public class CompoundAssignmentExpression implements Expr {
    private final Expr left;
    private final BinaryExpression.Operator op;
    private final Expr right;

    public CompoundAssignmentExpression(Expr left, BinaryExpression.Operator op, Expr right) {
        this.left = left;
        this.op = op;
        this.right = right;
    }

    public CompoundAssignmentExpression(ExtList list) {
        op = list.get(BinaryExpression.Operator.class);
        var exprs = list.collect(Expr.class);
        assert exprs.length == 2;
        left = exprs[0];
        right = exprs[1];
    }

    public Expr left() {
        return left;
    }

    public Expr right() {
        return right;
    }

    public BinaryExpression.Operator op() {
        return op;
    }

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
        return left + " " + op + "= " + right;
    }

    @Override
    public Type type(Services services) {
        return TupleType.UNIT;
    }
}
//spotless:on
