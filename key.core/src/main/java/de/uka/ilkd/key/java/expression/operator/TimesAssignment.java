/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;

/**
 * Times assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class TimesAssignment extends Assignment {

    /**
     * Times assignment.
     */

    public TimesAssignment() {}

    /**
     * Times assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public TimesAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY. The first occurrence of an
     * Expression in the given list is taken as the left hand side of the expression, the second
     * occurrence is taken as the right hand side of the expression.
     *
     * @param children the children of this AST element as KeY classes.
     */
    public TimesAssignment(ExtList children) {
        super(children);
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
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnTimesAssignment(this);
    }
}
