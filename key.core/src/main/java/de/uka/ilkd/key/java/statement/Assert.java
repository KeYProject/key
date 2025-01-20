/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;


public class Assert extends JavaStatement implements ExpressionContainer {

    private final Expression condition;
    private final Expression message;

    public Assert(Expression condition, Expression message, PositionInfo pos) {
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

    public Expression getMessage() {
        return message;
    }
}
