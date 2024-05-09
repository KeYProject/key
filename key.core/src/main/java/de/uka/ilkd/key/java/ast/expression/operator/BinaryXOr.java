/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Binary X or.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryXOr extends BinaryOperator {


    /**
     * Binary X or.
     *
     * @param children
     *        an ExtList with all children of this node the first children in list will be
     *        the one on the left side, the second the one on the right side.
     */

    public BinaryXOr(ExtList children) {
        super(children);
    }

    public BinaryXOr(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
    }


    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 8;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
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
        v.performActionOnBinaryXOr(this);
    }
}
