/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Negative.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Negative extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -7715433043154997463L;

    /**
     * Negative.
     */

    public Negative() {
        // nothing to do
    }

    /**
     * Negative.
     *
     * @param child an expression.
     */

    public Negative(Expression child) {
        super(child);
        makeParentRoleValid();
    }

    /**
     * Negative.
     *
     * @param proto a negative.
     */

    protected Negative(Negative proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Negative deepClone() {
        return new Negative(this);
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
        v.visitNegative(this);
    }
}
