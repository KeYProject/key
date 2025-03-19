/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Operator;

/**
 * Logical and.
 *
 * @author <TT>AutoDoc</TT>
 */

public class LogicalAnd extends Operator {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -2981535131033326663L;

    /**
     * Logical and.
     */

    public LogicalAnd() {
        // nothing to do
    }

    /**
     * Logical and.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public LogicalAnd(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Logical and.
     *
     * @param proto a logical and.
     */

    protected LogicalAnd(LogicalAnd proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public LogicalAnd deepClone() {
        return new LogicalAnd(this);
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
        return 10;
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
        v.visitLogicalAnd(this);
    }
}
