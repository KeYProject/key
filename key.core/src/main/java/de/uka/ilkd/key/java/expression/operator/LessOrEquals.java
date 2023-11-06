/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Less or equals.
 */

public class LessOrEquals extends ComparativeOperator {


    /**
     * Less or equals.
     *
     * @param children an ExtList with all children of this node the first children in list will be
     *        the one on the left side, the second the one on the right side.
     */

    public LessOrEquals(ExtList children) {
        super(children);
    }

    public LessOrEquals(Expression lhs, Expression rhs) {
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
        v.performActionOnLessOrEquals(this);
    }
}
