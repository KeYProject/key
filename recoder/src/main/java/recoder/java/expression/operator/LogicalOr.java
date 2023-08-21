/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Logical or.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LogicalOr extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 2782994601085095817L;

    /**
     * Logical or.
     */

    public LogicalOr() {
        // nothing to do
    }

    /**
     * Logical or.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public LogicalOr(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Logical or.
     *
     * @param proto a logical or.
     */

    protected LogicalOr(LogicalOr proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public LogicalOr deepClone() {
        return new LogicalOr(this);
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
        return 11;
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
        v.visitLogicalOr(this);
    }
}
