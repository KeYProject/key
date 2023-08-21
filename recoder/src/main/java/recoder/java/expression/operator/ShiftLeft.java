/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Shift left.
 *
 * @author <TT>AutoDoc</TT>
 */

public class ShiftLeft extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 840153660638293507L;

    /**
     * Shift left.
     */

    public ShiftLeft() {
        // nothing to do
    }

    /**
     * Shift left.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public ShiftLeft(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Shift left.
     *
     * @param proto a shift left.
     */

    protected ShiftLeft(ShiftLeft proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public ShiftLeft deepClone() {
        return new ShiftLeft(this);
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
        v.visitShiftLeft(this);
    }
}
