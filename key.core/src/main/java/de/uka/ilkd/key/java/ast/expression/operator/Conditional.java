/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/** The most weird ternary C operator ?: */

public class Conditional extends Operator {


    /**
     * Conditional.
     *
     * @param children
     *        list of children the first one is the guard expression, the second one the
     *        then expression and the last one the else expr.
     */

    public Conditional(ExtList children) {
        super(children);
    }

    public Conditional(
            PositionInfo pi, List<Comment> c, Expression accept, Expression accept1,
            Expression accept2) {
        super(pi, c, new ImmutableArray<>(accept, accept1, accept2));
    }


    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 3;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 12;
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
     * Checks if this operator is left or right associative. Conditionals are right associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnConditional(this);
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();
        final KeYJavaType type1 = tc.getKeYJavaType(getExpressionAt(1), ec);
        final KeYJavaType type2 = tc.getKeYJavaType(getExpressionAt(2), ec);
        if (tc.isIdentical(type1, type2)) {
            return type1;
        }

        // numeric types
        if (tc.isNumericalType(type1) && tc.isNumericalType(type2)) {
            if (type1.getJavaType() == PrimitiveType.JAVA_BYTE
                    && type2.getJavaType() == PrimitiveType.JAVA_SHORT
                    || type1.getJavaType() == PrimitiveType.JAVA_SHORT
                            && type2.getJavaType() == PrimitiveType.JAVA_BYTE) {
                return javaServ.getJavaInfo().getKeYJavaType(PrimitiveType.JAVA_SHORT);
            }
            if (tc.isImplicitNarrowing(getExpressionAt(1), (PrimitiveType) type2.getJavaType())) {
                return type2;
            }
            if (tc.isImplicitNarrowing(getExpressionAt(2), (PrimitiveType) type1.getJavaType())) {
                return type1;
            }
            return tc.getPromotedType(type1, type2);
        }


        // reference types
        if (tc.isNullType(type1) && tc.isReferenceType(type2)) {
            return type2;
        }
        if (tc.isNullType(type2) && tc.isReferenceType(type1)) {
            return type1;
        }
        if (tc.isAssignableTo(type1, type2)) {
            return type2;
        }
        if (tc.isAssignableTo(type2, type1)) {
            return type1;
        }

        throw new RuntimeException("Could not determine type of conditional " + "expression\n"
            + this + ". This usually means that " + "the Java program is not compilable.");
    }

}
