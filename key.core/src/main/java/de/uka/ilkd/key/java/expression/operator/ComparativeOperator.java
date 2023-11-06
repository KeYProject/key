/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.expression.operator;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.reference.ExecutionContext;

import org.key_project.util.ExtList;

/**
 * Comparative operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class ComparativeOperator extends Operator {


    /**
     * Comparative operator.
     *
     * @param children an ExtList with all children of this node the first children in list will be
     *        the one on the left side, the second the one on the right side.
     */

    public ComparativeOperator(ExtList children) {
        super(children);
    }

    public ComparativeOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
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
