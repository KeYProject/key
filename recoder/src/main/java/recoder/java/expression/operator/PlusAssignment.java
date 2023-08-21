/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.java.expression.operator;

import recoder.java.Expression;
import recoder.java.SourceVisitor;
import recoder.java.expression.Assignment;

/**
 * Addition or string concatenation assignment "+=".
 */

public class PlusAssignment extends Assignment {

    /**
     * serialization id
     */
    private static final long serialVersionUID = 316506987506404732L;

    /**
     * Plus assignment.
     */

    public PlusAssignment() {
        // nothing to do
    }

    /**
     * Plus assignment.
     *
     * @param lhs an expression.
     * @param rhs an expression.
     */

    public PlusAssignment(Expression lhs, Expression rhs) {
        super(lhs, rhs);
        makeParentRoleValid();
    }

    /**
     * Plus assignment.
     *
     * @param proto a plus assignment.
     */

    protected PlusAssignment(PlusAssignment proto) {
        super(proto);
        makeParentRoleValid();
    }

    /**
     * Deep clone.
     *
     * @return the object.
     */

    public PlusAssignment deepClone() {
        return new PlusAssignment(this);
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
        v.visitPlusAssignment(this);
    }
}
