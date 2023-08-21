/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Divide assignment.
 *
 * @author <TT>AutoDoc</TT>
 */

public class DivideAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 3806208146891527861L;

    /**
     * Divide assignment.
     */

    public DivideAssignment() {
        // nothing to do
    }

    /**
     * Divide assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public DivideAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Divide assignment.
     *
     * @param proto a divide assignment.
     */

    protected DivideAssignment(DivideAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public DivideAssignment deepClone() {
        return new DivideAssignment(this);
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
        v.visitDivideAssignment(this);
    }
}
