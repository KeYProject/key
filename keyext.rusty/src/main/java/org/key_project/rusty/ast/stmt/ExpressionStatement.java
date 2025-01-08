/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.stmt;

import org.key_project.logic.SyntaxElement;
import org.key_project.rusty.ast.expr.Expr;
import org.key_project.rusty.ast.visitor.Visitor;
import org.key_project.rusty.logic.PosInProgram;
import org.key_project.rusty.logic.PossibleProgramPrefix;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.NonNull;

public class ExpressionStatement implements Statement, PossibleProgramPrefix {
    private final Expr expression;
    private final boolean semi;

    public ExpressionStatement(Expr expression, boolean semi) {
        this.expression = expression;
        this.semi = semi;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        if (n == 0) {
            return expression;
        }
        throw new IndexOutOfBoundsException("ExpressionStatement has only one child.");
    }

    public Expr getExpression() {
        return expression;
    }

    public boolean hasSemi() {
        return semi;
    }

    @Override
    public int getChildCount() {
        return 1;
    }

    @Override
    public String toString() {
        return expression.toString() + ";";
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnExpressionStatement(this);
    }

    @Override
    public boolean isPrefix() {
        return getChildCount() != 0 && expression instanceof PossibleProgramPrefix pre
                && pre.isPrefix();
    }

    @Override
    public boolean hasNextPrefixElement() {
        return getChildCount() != 0 && expression instanceof PossibleProgramPrefix;
    }

    @Override
    public PossibleProgramPrefix getNextPrefixElement() {
        if (hasNextPrefixElement()) {
            return (PossibleProgramPrefix) expression;
        }
        throw new IndexOutOfBoundsException("No next prefix element " + this);
    }

    @Override
    public PossibleProgramPrefix getLastPrefixElement() {
        return hasNextPrefixElement() ? getNextPrefixElement().getLastPrefixElement() : this;
    }

    @Override
    public ImmutableArray<PossibleProgramPrefix> getPrefixElements() {
        if (hasNextPrefixElement()) {
            return new ImmutableArray<>((PossibleProgramPrefix) expression);
        }
        return new ImmutableArray<>();
    }

    @Override
    public PosInProgram getFirstActiveChildPos() {
        return PosInProgram.ZERO;
    }

    @Override
    public int getPrefixLength() {
        return hasNextPrefixElement() ? 1 : 0;
    }

    @Override
    public int hashCode() {
        return expression.hashCode();
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null || getClass() != obj.getClass())
            return false;
        ExpressionStatement that = (ExpressionStatement) obj;
        return expression.equals(that.expression);
    }
}
