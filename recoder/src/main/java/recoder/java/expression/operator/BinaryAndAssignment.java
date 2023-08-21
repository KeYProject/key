/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Binary and assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class BinaryAndAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = -5443127019426961308L;

    /**
     * Binary and assignment.
     */

    public BinaryAndAssignment() {
        // nothing to do
    }

    /**
     * Binary and assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public BinaryAndAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Binary and assignment.
     *
     * @param proto a binary and assignment.
     */

    protected BinaryAndAssignment(BinaryAndAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public BinaryAndAssignment deepClone() {
        return new BinaryAndAssignment(this);
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
        return 13;
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
        v.visitBinaryAndAssignment(this);
    }
}
