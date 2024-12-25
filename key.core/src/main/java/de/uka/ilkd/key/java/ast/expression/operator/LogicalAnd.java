/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

/**
 * Logical and.
 */

public class LogicalAnd extends Operator {

    public LogicalAnd(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public LogicalAnd(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c, new ImmutableArray<>(lhs, rhs));

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
        return 10;
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
        v.performActionOnLogicalAnd(this);
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        return services.getTypeConverter().getBooleanType();
    }

}
