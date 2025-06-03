/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Operator of arity 2
 *
 * @author AL
 */
public abstract class BinaryOperator extends Operator {

    protected BinaryOperator(ExtList children) {
        super(children);
    }

    protected BinaryOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public BinaryOperator(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
        super(pi, c,
            new ImmutableArray<>(Objects.requireNonNull(lhs), Objects.requireNonNull(rhs)));
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */
    public int getArity() {
        return 2;
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        final TypeConverter tc = javaServ.getTypeConverter();
        try {
            return tc.getPromotedType(tc.getKeYJavaType((Expression) getChildAt(0), ec),
                tc.getKeYJavaType((Expression) getChildAt(1), ec));
        } catch (Exception e) {
            throw new RuntimeException("Type promotion failed (see below). Operator was " + this,
                e);
        }
    }

}
