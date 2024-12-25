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
 * Equals.
 */
public class Equals extends ComparativeOperator {
    /**
     * Creates the equals expression <code>lhs==rhs</code>
     *
     * @param lhs
     *        the Expression on the left side of the comparison
     * @param rhs
     *        the Expression on the right side of the comparison
     */
    public Equals(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public Equals(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 6;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnEquals(this);
    }
}
