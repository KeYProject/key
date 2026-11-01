/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.ExpressionContainer;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

@NullMarked
public class Assert extends JavaStatement implements ExpressionContainer {

    private final Expression condition;
    private final @Nullable Expression message;

    public Assert(Expression condition, @Nullable Expression message, PositionInfo pos) {
        super(pos);
        assert condition != null;
        this.condition = condition;
        this.message = message;
    }


    public Expression getExpressionAt(int index) {
        if (index == 0) {
            return condition;
        }
        index--;
        if (index == 0) {
            if (message != null) {
                return message;
            }
        }
        throw new IndexOutOfBoundsException();
    }

    public int getExpressionCount() {
        return message == null ? 1 : 2;
    }

    public ProgramElement getChildAt(int index) {
        return getExpressionAt(index);
    }

    public int getChildCount() {
        return getExpressionCount();
    }

    public void visit(Visitor v) {
        v.performActionOnAssert(this);
    }

    public Expression getCondition() {
        return condition;
    }

    public @Nullable Expression getMessage() {
        return message;
    }
}
