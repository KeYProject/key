/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.TypeConverter;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.jspecify.annotations.Nullable;

import java.util.List;

/**
 * Shift left.
 */
public class ShiftLeft extends Operator {
    /**
     * Shift left.
     *
     * @param lhs
     *        an expression.
     * @param rhs
     *        an expression.
     */
    public ShiftLeft(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public ShiftLeft(@Nullable PositionInfo pi, @Nullable List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, lhs, rhs);
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
        return 4;
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
        v.performActionOnShiftLeft(this);
    }


    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();
        return tc.getPromotedType(tc.getKeYJavaType((Expression) getChildAt(0), ec));
    }
}
