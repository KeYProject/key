/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Shift left assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ShiftLeftAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 2965087191992910283L;

    /**
     * Shift left assignment.
     */

    public ShiftLeftAssignment() {
        // nothing to do
    }

    /**
     * Shift left assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public ShiftLeftAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Shift left assignment.
     *
     * @param proto a shift left assignment.
     */

    protected ShiftLeftAssignment(ShiftLeftAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ShiftLeftAssignment deepClone() {
        return new ShiftLeftAssignment(this);
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
        v.visitShiftLeftAssignment(this);
    }
}
