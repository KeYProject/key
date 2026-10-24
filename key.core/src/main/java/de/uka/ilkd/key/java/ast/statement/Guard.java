/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class Guard extends JavaNonTerminalProgramElement implements IGuard {

    final Expression expr;

    public Guard(Expression expression) {
        expr = expression;
    }

    public Guard(ExtList children) {
        expr = Objects.requireNonNull(children.get(Expression.class),
            "a guard requires an expression");
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

    // a guard has at most one child (the required expression); an out-of-range index returns null,
    // which conflicts with the @NonNull contract of NonTerminalProgramElement.getChildAt(int), but
    // the base contract is over-narrow; honest @Nullable override per SuperArrayDeclaration
    // precedent (wave 7).
    @SuppressWarnings("NullAway")
    public @Nullable ProgramElement getChildAt(int index) {
        if (index == 0) {
            return expr;
        }
        return null;
    }

    public String toString() {
        return expr.toString();
    }
}
