/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

public class Guard extends JavaNonTerminalProgramElement implements IGuard {

    final Expression expr;

    public Guard(Expression expression) {
        expr = expression;
    }

    public Guard(ExtList children) {
        expr = children.get(Expression.class);
    }

    public Guard(PositionInfo pi, List<Comment> o1, Expression expression) {
        super(pi, o1);
        this.expr = expression;
    }

    public Expression getExpression() {
        return expr;
    }

    public void visit(Visitor v) {
        v.performActionOnGuard(this);
    }

    public int getChildCount() {
        return (expr != null) ? 1 : 0;
    }

    public ProgramElement getChildAt(int index) {
        if (index == 0) { return expr; }
        return null;
    }

    public String toString() {
        return expr.toString();
    }
}
