/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Binary not.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryNot extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6494982658640409026L;

    /**
     * Binary not.
     */

    public BinaryNot() {
        // nothing to do
    }

    /**
     * Binary not.
     *
     * @param child an expression.
     */

    public BinaryNot(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Binary not.
     *
     * @param proto a binary not.
     */

    protected BinaryNot(BinaryNot proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryNot deepClone() {
        return new BinaryNot(this);
    }

    /**
     * Get arity.
     *
     * @return the int value.
     */

    public int getArity() {
        return 1;
    }

    /**
     * Get precedence.
     *
     * @return the int value.
     */

    public int getPrecedence() {
        return 1;
    }

    /**
     * Get notation.
     *
     * @return the int value.
     */

    public int getNotation() {
        return PREFIX;
    }

    /**
     * Checks if this operator is left or right associative. Ordinary unary operators are right
     * associative.
     *
     * @return <CODE>true</CODE>, if the operator is left associative, <CODE>
     * false</CODE> otherwise.
     */

    public boolean isLeftAssociative() {
        return false;
    }

    public void accept(SourceVisitor v) {
        v.visitBinaryNot(this);
    }
}
