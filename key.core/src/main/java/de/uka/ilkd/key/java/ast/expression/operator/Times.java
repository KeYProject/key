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
 * Times.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Times extends BinaryOperator {

    /**
     * Times.
     *
     * @param lhs
     *        an expression.
     * @param rhs
     *        an expression.
     */

    public Times(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY. The first occurrence of an
     * Expression in the given list is taken as the left hand side of the expression, the second
     * occurrence is taken as the right hand side of the expression.
     *
     * @param children
     *        the children of this AST element as KeY classes.
     */
    public Times(ExtList children) {
        super(children);
    }

    public Times(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
    }


    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 2;
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
        v.performActionOnTimes(this);
    }


}
