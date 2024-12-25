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
 * Less than.
 */
public class LessThan extends ComparativeOperator {
    /**
     * Less than.
     *
     * @param lhs
     *        the expression that is checked to be less than rhs
     * @param rhs
     *        the expression that is checked to be greater than lhs
     */
    public LessThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public LessThan(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
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
        v.performActionOnLessThan(this);
    }
}
