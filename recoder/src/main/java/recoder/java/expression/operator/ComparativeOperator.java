/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.expression.Operator;

/**
 * Comparative operator.
 *
 * @author <TT>AutoDoc</TT>
 */

public abstract class ComparativeOperator extends Operator {

    /**
     * Comparative operator.
     */

    public ComparativeOperator() {
        super();
    }

    /**
     * Comparative operator.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public ComparativeOperator(Expression lhs, Expression rhs) {
        super(lhs, rhs);
    }

    /**
     * Comparative operator.
     *
     * @param proto a comparative operator.
     */

    protected ComparativeOperator(ComparativeOperator proto) {
        super(proto);
        makeParentRoleValid();
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
}
