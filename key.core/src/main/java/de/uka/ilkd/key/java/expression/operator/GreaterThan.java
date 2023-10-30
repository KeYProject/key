/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Greater than.
 */

public class GreaterThan extends ComparativeOperator {


    /**
     * Greater than.
     *
     * @param children an ExtList with all children of this node the first children in list will be
     *        the one on the left side, the second the one on the right side.
     */

    public GreaterThan(ExtList children) {
        super(children);
    }

    /**
     * Greater than.
     *
     * @param lhs the expression that is checked to be greater than rhs
     * @param rhs the expression that is checked to be less than lhs
     */
    public GreaterThan(Expression lhs, Expression rhs) {
        super(lhs, rhs);
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
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnGreaterThan(this);
    }
}
