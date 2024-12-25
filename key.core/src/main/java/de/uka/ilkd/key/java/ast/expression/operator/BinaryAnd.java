/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.visitor.Visitor;

import java.util.List;

/**
 * Binary and.
 */
public class BinaryAnd extends BinaryOperator {
    public BinaryAnd(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public final int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public final int getPrecedence() {
        return 7;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public final int getNotation() {
        return Operator.INFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnBinaryAnd(this);
    }


}
