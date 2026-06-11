/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Shift left assignment.
 */

public class ShiftLeftAssignment extends Assignment {

    /**
     * Shift left assignment.
     */

    public ShiftLeftAssignment() {}

    /**
     * Shift left assignment.
     *
     * @param lhs
     *        an expression.
     * @param rhs
     *        an expression.
     */

    public ShiftLeftAssignment(Expression lhs, Expression rhs) {
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
    public ShiftLeftAssignment(ExtList children) {
        super(children);
    }

    public ShiftLeftAssignment(PositionInfo pi, List<Comment> c, Expression target,
            Expression expr) {
        super(pi, c, target, expr);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 13;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return INFIX;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnShiftLeftAssignment(this);
    }
}
