/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Binary and.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryAnd extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 5167112677525923924L;

    /**
     * Binary and.
     */

    public BinaryAnd() {
        // nothing to do
    }

    /**
     * Binary and.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public BinaryAnd(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Binary and.
     *
     * @param proto a binary and.
     */

    protected BinaryAnd(BinaryAnd proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryAnd deepClone() {
        return new BinaryAnd(this);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public final int getArity() {
        return 2;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public final int getPrecedence() {
        return 7;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public final int getNotation() {
        return INFIX;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryAnd(this);
    }
}
