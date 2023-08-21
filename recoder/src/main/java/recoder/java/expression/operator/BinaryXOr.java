/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Binary X or.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryXOr extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7163139482513251225L;

    /**
     * Binary X or.
     */

    public BinaryXOr() {
        // nothing to do
    }

    /**
     * Binary X or.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public BinaryXOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Binary X or.
     *
     * @param proto a binary X or.
     */

    protected BinaryXOr(BinaryXOr proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryXOr deepClone() {
        return new BinaryXOr(this);
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
        return 8;
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
        v.visitBinaryXOr(this);
    }
}
