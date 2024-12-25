/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;


/**
 * An assignment is an operator with side-effects.
 */

public abstract class Assignment extends Operator implements ExpressionStatement {
    /**
     * Unary Assignment (e.g. +=, ++).
     *
     * @param lhs an expression.
     */
    public Assignment(Expression lhs) {
        this(null, null, lhs);
    }

    /**
     * Assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */
    public Assignment(Expression lhs, Expression rhs) {
        this(null, null, lhs, rhs);
    }

    public Assignment(@Nullable PositionInfo pi, @Nullable List<Comment> c, Expression target, Expression expr) {
        super(pi, c, new ImmutableArray<>(target, expr));
    }

    public Assignment(@Nullable PositionInfo pi, @Nullable List<Comment> c, Expression child) {
        super(pi, c, new ImmutableArray<>(child));
    }


    /**
     * Checks if this operator is left or right associative. Assignments are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }


    /**
     * retrieves the type of the assignment expression
     *
     * @param javaServ the Services offering access to the Java model
     * @param ec       the ExecutionContext in which the expression is evaluated
     * @return the type of the assignment expression
     */
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return getExpressionAt(0).getKeYJavaType(javaServ, ec);
    }


    /**
     * overriden from Operator
     */
    public String reuseSignature(Services services, ExecutionContext ec) {
        String base = super.reuseSignature(services, ec);
        Expression rhs;
        try {
            rhs = children.get(1);
        } catch (ArrayIndexOutOfBoundsException e) {
            // no second argument, e.g. PostIncrement
            return base;
        }
        if (rhs instanceof BooleanLiteral) {
            return base + "[" + rhs + "]";
        } else {
            return base;
        }
    }

}
