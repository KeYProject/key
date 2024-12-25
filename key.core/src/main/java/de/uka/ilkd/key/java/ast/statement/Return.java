/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Return.
 */

public class Return extends ExpressionJumpStatement {
    /**
     * Expression jump statement.
     *
     * @param expr an Expression used to jump
     */
    public Return(Expression expr) {
        super(expr);
    }

    public Return(@Nullable PositionInfo pi, @Nullable List<Comment> comments, Expression expr) {
        super(pi, comments, expr);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnReturn(this);
    }
}
