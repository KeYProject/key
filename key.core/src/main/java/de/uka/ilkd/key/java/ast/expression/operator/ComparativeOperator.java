/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

/**
 * Comparative operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class ComparativeOperator extends Operator {


    /**
     * Comparative operator.
     *
     * @param children
     *        an ExtList with all children of this node the first children in list will be
     *        the one on the left side, the second the one on the right side.
     */

    public ComparativeOperator(ExtList children) {
        super(children);
    }

    public ComparativeOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    public ComparativeOperator(PositionInfo pi, List<Comment> c, Expression lhs, Expression rhs) {
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
