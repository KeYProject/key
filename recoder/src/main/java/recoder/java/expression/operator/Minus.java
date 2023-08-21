/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Minus.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Minus extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 6139443256879639859L;

    /**
     * Minus.
     */

    public Minus() {
        // nothing to do
    }

    /**
     * Minus.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Minus(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Minus.
     *
     * @param proto a minus.
     */

    protected Minus(Minus proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Minus deepClone() {
        return new Minus(this);
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
        v.visitMinus(this);
    }
}
