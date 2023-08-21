/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Unsigned shift right.
 *
 * @author <TT>AutoDoc</TT>
 */

public class UnsignedShiftRight extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 638313602392128439L;

    /**
     * Unsigned shift right.
     */

    public UnsignedShiftRight() {
        // nothing to do
    }

    /**
     * Unsigned shift right.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public UnsignedShiftRight(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Unsigned shift right.
     *
     * @param proto an unsigned shift right.
     */

    protected UnsignedShiftRight(UnsignedShiftRight proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public UnsignedShiftRight deepClone() {
        return new UnsignedShiftRight(this);
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
        v.visitUnsignedShiftRight(this);
    }
}
