/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.pat;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.expr.LiteralExpression;
import org.key_project.rusty.ast.expr.UnaryExpression;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.util.ExtList;

public class LitPatExpr implements PatExpr {
    private final LiteralExpression lit;
    private final boolean negated;

    public LitPatExpr(LiteralExpression lit, boolean negated) {
        this.lit = lit;
        this.negated = negated;
    }

    public LitPatExpr(ExtList changeList, boolean negated) {
        this.lit = changeList.get(LiteralExpression.class);
        this.negated = negated;
    }

    public LiteralExpression getLit() {
        return lit;
    }

    public boolean isNegated() {
        return negated;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLitPatExpr(this);
    }

    @Override
    public SyntaxElement getChild(int n) {
        if (n == 0)
            return lit;
        throw new IndexOutOfBoundsException("LitPatExpr has only one child");
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        if (negated)
            return "-" + lit;
        else
            return lit.toString();
    }

    @Override
    public Expr toExpr() {
        if (negated)
            return new UnaryExpression(UnaryExpression.Operator.Neg, lit);
        else
            return lit;
    }
}
