/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Divide assignment.
 */
public class DivideAssignment extends Assignment {
    public DivideAssignment(@Nullable PositionInfo pi, @Nullable List<Comment> c, Expression target, Expression expr) {
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
     * @param v the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnDivideAssignment(this);
    }
}
