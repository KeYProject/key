/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Times.
 *
 * @author <TT>AutoDoc</TT>
 */

public class Times extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 452019546318592957L;

    /**
     * Times.
     */

    public Times() {
        // nothing to do
    }

    /**
     * Times.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public Times(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Times.
     *
     * @param proto a times.
     */

    protected Times(Times proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public Times deepClone() {
        return new Times(this);
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
        return 2;
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
        v.visitTimes(this);
    }
}
