/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Shift right.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ShiftRight extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -3676799631907980532L;

    /**
     * Shift right.
     */

    public ShiftRight() {
        // nothing to do
    }

    /**
     * Shift right.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public ShiftRight(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Shift right.
     *
     * @param proto a shift right.
     */

    protected ShiftRight(ShiftRight proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ShiftRight deepClone() {
        return new ShiftRight(this);
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
        return 4;
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
        v.visitShiftRight(this);
    }
}
