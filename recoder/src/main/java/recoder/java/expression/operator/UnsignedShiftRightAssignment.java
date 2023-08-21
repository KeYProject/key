/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Unsigned shift right assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class UnsignedShiftRightAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 1895345140424768114L;

    /**
     * Unsigned shift right assignment.
     */

    public UnsignedShiftRightAssignment() {
        // nothing to do
    }

    /**
     * Unsigned shift right assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public UnsignedShiftRightAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Unsigned shift right assignment.
     *
     * @param proto an unsigned shift right assignment.
     */

    protected UnsignedShiftRightAssignment(UnsignedShiftRightAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public UnsignedShiftRightAssignment deepClone() {
        return new UnsignedShiftRightAssignment(this);
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
        v.visitUnsignedShiftRightAssignment(this);
    }
}
