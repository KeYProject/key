/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Addition or string concatenation operator "+".
 */

public class Plus extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 560126060000682104L;

    /**
     * Plus.
     */

    public Plus() {
        // nothing to do
    }

    /**
     * Plus.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Plus(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Plus.
     *
     * @param proto a plus.
     */

    protected Plus(Plus proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Plus deepClone() {
        return new Plus(this);
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
        return 3;
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
        v.visitPlus(this);
    }
}
