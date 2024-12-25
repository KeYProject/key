/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import java.util.List;

/**
 * Greater than.
 */
public class GreaterThan extends ComparativeOperator {
    /**
     * Greater than.
     *
     * @param lhs
     *        the expression that is checked to be greater than rhs
     * @param rhs
     *        the expression that is checked to be less than lhs
     */
    public GreaterThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public GreaterThan(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 5;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnGreaterThan(this);
    }
}
