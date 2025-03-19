/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Binary or.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryOr extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7549894415250172486L;

    /**
     * Binary or.
     */

    public BinaryOr() {
        // nothing to do
    }

    /**
     * Binary or.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public BinaryOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Binary or.
     *
     * @param proto a binary or.
     */

    protected BinaryOr(BinaryOr proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryOr deepClone() {
        return new BinaryOr(this);
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
        return 9;
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
        v.visitBinaryOr(this);
    }
}
