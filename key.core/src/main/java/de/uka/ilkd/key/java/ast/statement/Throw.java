/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.statement;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Throw.
 */

public class Throw extends ExpressionJumpStatement {

    /**
     * Throw.
     */

    public Throw() {}

    /**
     * Throw.
     *
     * @param expr
     *        an expression.
     */

    public Throw(Expression expr) {
        super(expr);
        if (expr == null) {
            throw new IllegalArgumentException("Throw requires one argument");
        }
    }

    /**
     * Throw.
     *
     * @param children
     *        an ExtList with all children
     */

    public Throw(ExtList children) {
        super(children);
    }

    /**
     * Throw.
     *
     */

    public Throw(Expression expression, PositionInfo pi, List<Comment> comments) {
        super(expression, pi, comments);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnThrow(this);
    }
}
