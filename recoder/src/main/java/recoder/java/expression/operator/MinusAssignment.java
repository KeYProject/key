/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Minus assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class MinusAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -1043954220632471820L;

    /**
     * Minus assignment.
     */

    public MinusAssignment() {
        // nothing to do
    }

    /**
     * Minus assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public MinusAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Minus assignment.
     *
     * @param proto a minus assignment.
     */

    protected MinusAssignment(MinusAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public MinusAssignment deepClone() {
        return new MinusAssignment(this);
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

    public void accept(SourceVisitor v) {
        v.visitMinusAssignment(this);
    }
}
