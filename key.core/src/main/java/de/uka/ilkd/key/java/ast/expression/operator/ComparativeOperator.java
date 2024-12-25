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
import org.jspecify.annotations.Nullable;
import org.key_project.util.collection.ImmutableArray;

import java.util.List;

/**
 * Comparative operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class ComparativeOperator extends Operator {
    public ComparativeOperator(Expression lhs, Expression rhs) {
        this(null, null, lhs, rhs);
    }

    public ComparativeOperator(@Nullable PositionInfo pi,@Nullable List<Comment> c, Expression lhs, Expression rhs) {
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
     * Get notation.
     *
     * @return the int value.
     */
    public int getNotation() {
        return INFIX;
    }

    public KeYJavaType getKeYJavaType(Services services, ExecutionContext ec) {
        return getKeYJavaType(services);
    }

    public KeYJavaType getKeYJavaType(Services services) {
        return services.getTypeConverter().getBooleanType();
    }

}
